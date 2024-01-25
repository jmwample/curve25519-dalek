// -*- mode: rust; -*-

//! Functions mapping curve points to representative values
//! (indistinguishable from random), and back again.
use crate::constants::{MONTGOMERY_A, MONTGOMERY_A_NEG};
use crate::field::FieldElement;
use crate::montgomery::MontgomeryPoint;
use crate::EdwardsPoint;

use subtle::{
    Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
    CtOption,
};

/// (p - 1) / 2 = 2^254 - 10
pub(crate) const DIVIDE_MINUS_P_1_2_BYTES: [u8; 32] = [
    0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
];

/// Gets the public representative for a key pair using the private key
pub fn representative_from_privkey(privkey: &[u8; 32]) -> Option<[u8; 32]> {
    let pubkey = EdwardsPoint::mul_base_clamped(privkey.clone()).to_montgomery();
    let v_in_sqrt = v_in_sqrt(privkey);
    point_to_representative(&pubkey, v_in_sqrt.into()).into()
}

/// This function is used to map a curve point (i.e. an x25519 public key)
/// to a point that is effectively indistinguishable from random noise.
///
/// This operation may fail because not all curve points are capable of being
/// hidden. On failure, this function will return None.
///
/// This implementation is adapted from both:
/// - [kleshni C implementation](https://github.com/Kleshni/Elligator-2)
/// - [agl/ed25519 golang forks](https://gitlab.com/yawning/edwards25519-extra)
///
///
/// Note: the output field elements of this function are uniformly
/// distributed among the nonnegative field elements, but only if the
/// input points are also uniformly distributed among all points of
/// the curve. In particular, if the inputs are only selected from
/// members of the prime order group, then the outputs are
/// distinguishable from random.
///
/// # Inputs
///
/// * `point`: the \\(u\\)-coordinate of a point on the curve. Not all
/// points map to field elements.
///
/// * `v_in_sqrt`: true if the \\(v\\)-coordinate of the point is negative.
///
/// # Returns
///
/// Either `None`, if the point couldn't be mapped, or `Some(fe)` such
/// that `fe` is nonnegative and `map_to_point(&fe) == point`.
///
/// [elligator paper](https://elligator.cr.yp.to/elligator-20130828.pdf)
/// [elligator site](https://elligator.org/)
///
pub fn point_to_representative(point: &MontgomeryPoint, v_in_sqrt: bool) -> CtOption<[u8; 32]> {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // a := point
    let a = &FieldElement::from_bytes(&point.0);
    let mut a_neg = a.clone();
    a_neg.negate();

    let is_encodable = is_encodable(a);

    // Calculate r1 = sqrt(-a/(2*(a+A)))
    let (_r1_sqrt, r1) = FieldElement::sqrt_ratio_i(
        &a_neg,
        &(&(a + &MONTGOMERY_A) * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // Calculate  r0 = sqrt(-(a+A)/(2a))
    let (_r0_sqrt, r0) = FieldElement::sqrt_ratio_i(
        &(&a_neg - &MONTGOMERY_A),
        &(a * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // if v_in_sqrt root=r0 otherwise r1
    let mut b = FieldElement::conditional_select(&r1, &r0, Choice::from(v_in_sqrt as u8));

    // If root > (p - 1) / 2, root := -root
    let negate = divide_minus_p_1_2.ct_gt(&b);
    FieldElement::conditional_negate(&mut b, negate);

    CtOption::new(b.as_bytes(), is_encodable)
}

/// Determines whether a point is encodable as a representative. Approximately
/// 50% of points are not encodable.
#[inline]
fn is_encodable(u: &FieldElement) -> Choice {
    let b0 = u + &MONTGOMERY_A;
    let b1 = &(&(&b0.square().square() * &b0.square()) * &b0) * u; // b1 = u * (u + A)^7
    let c = b1.pow_p58();

    let b2 = &(&b0.square().square().square() * &b0.square().square()) * &b0.square(); // (u + A)^14
    let mut chi = &(&c.square().square() * &u.square()) * &b2; // chi = -c^4 * u^2 * (u + A)^14
    chi.negate();

    let chi_bytes = chi.as_bytes();

    // chi[1] is either 0 or 0xff
    chi_bytes[1].ct_eq(&0_u8)
}

///  `high_y` - Montgomery points can have have two different values for a
///  single X coordinate (based on sign). The Kleshni implementation determines
///  which sign value to use with this function.
///
///  If the point is 0, this should be ignored.
#[inline]
pub(crate) fn high_y(d: &FieldElement) -> Choice {
    let d_sq = &d.square();
    let au = &MONTGOMERY_A * &d;

    let inner = &(d_sq + &au) + &FieldElement::ONE;
    let eps = d * &inner; /* eps = d^3 + Ad^2 + d */

    let (eps_is_sq, _) = FieldElement::sqrt_ratio_i(&eps, &FieldElement::ONE);

    eps_is_sq
}

/// Determines if `V <= (p - 1)/2` for a Scalar (e.g an x25519 private key) and
/// returns a [`Choice`] indicating the result.
///
/// Note: When using the elligator2 transformations on x25519 keypairs this
/// requires the use of the clamped scalar_base_mult of the private key to
/// get the edwards representation of the public key, otherwise we need to know
/// the correct sign value for the edwards conversion or the derivation of
/// the `V` value will be broken. As noted in [`EdwardsPoint::to_montgomery`],
/// the sign information about the X coordinate is lost on conversion so we
/// have to use the edwards point derived from the private key to guarantee the
/// correct value here.
///
/// Alternatively you can keep track of the public key and sign bit manually
/// and construct an EdwardsPoint for which [`v_in_sqrt_pubkey_edwards`] will
/// give you the same result.
///
// As an interface, using the private key should work just fine. This allows
// us to match the existing [`PublicKey`] generation interface for the
// [`PublicRepresentative`] in the [`x25519_dalek`] crate. AFAIK there is no
// need for anyone with only the public key to be able to generate the
// representative.
pub fn v_in_sqrt(key_input: &[u8; 32]) -> Choice {
    let mut masked_pk = key_input.clone();
    masked_pk[0] &= 0xf8;
    masked_pk[31] &= 0x7f;
    masked_pk[31] |= 0x40;

    let pubkey = EdwardsPoint::mul_base_clamped(masked_pk);
    v_in_sqrt_pubkey_edwards(&pubkey)
}

/// Determines if `V <= (p - 1)/2` for an EdwardsPoint (e.g an x25519 public key)
/// and returns a [`Choice`] indicating the result.
pub fn v_in_sqrt_pubkey_edwards(pubkey: &EdwardsPoint) -> Choice {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // sqrtMinusAPlus2 is sqrt(-(486662+2))
    let (_, sqrt_minus_a_plus_2) = FieldElement::sqrt_ratio_i(
        &(&MONTGOMERY_A_NEG - &(&FieldElement::ONE + &FieldElement::ONE)),
        &FieldElement::ONE,
    );

    // inv1 = 1/((A.Z - A.y) * A.X)
    let inv1 = (&(&pubkey.Z - &pubkey.Y) * &pubkey.X).invert();

    // t0 = A.Y + A.Z
    let t0 = &pubkey.Y + &pubkey.Z;

    // v = t0 * inv1 * A.Z * sqrtMinusAPlus2
    let v = &(&t0 * &inv1) * &(&pubkey.Z * &sqrt_minus_a_plus_2);

    // is   v <= (q-1)/2  ?
    let c = divide_minus_p_1_2.ct_gt(&v);

    c
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

#[allow(unused, non_snake_case)]
/// Perform the Elligator2 mapping to a Montgomery point.
///
/// See <https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10#section-6.7.1>
//
// TODO Determine how much of the hash-to-group API should be exposed after the CFRG
//      draft gets into a more polished/accepted state.
pub fn map_to_point(r: &[u8; 32]) -> FieldElement {
    let r_0 = FieldElement::from_bytes(r);
    let one = FieldElement::ONE;
    let d_1 = &one + &r_0.square2(); /* 2r^2 */

    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* A/(1+2r^2) */

    let eps_is_sq = high_y(&d);

    let zero = FieldElement::ZERO;
    let Atemp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq); /* 0, or A if nonsquare*/
    let mut u = &d + &Atemp; /* d, or d+A if nonsquare */
    u.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    u
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod test {
    use super::*;

    const MASK_UNSET_BYTE: u8 = 0x3f;

    ////////////////////////////////////////////////////////////
    // Ntor tests                                             //
    ////////////////////////////////////////////////////////////

    #[test]
    #[cfg(feature = "elligator2")]
    fn repres_from_pubkey_kleshni() {
        // testcases from kleshni
        for (i, testcase) in encoding_testcases().iter().enumerate() {
            let point: [u8; 32] = hex::decode(testcase.point).unwrap().try_into().unwrap();

            let edw_point = MontgomeryPoint(point)
                .to_edwards(testcase.high_y as u8)
                .unwrap();
            let v_in_sqrt = v_in_sqrt_pubkey_edwards(&edw_point);

            let repres: Option<[u8; 32]> =
                point_to_representative(&MontgomeryPoint(point), v_in_sqrt.into()).into();
            if testcase.representative.is_some() {
                assert_eq!(
                    testcase.representative.unwrap(),
                    hex::encode(repres.unwrap()),
                    "[good case] kleshni ({i}) bad pubkey from true representative"
                );
            } else {
                assert!(
                    repres.is_none(),
                    "[good case] kleshni ({i}) expected none got repres {}",
                    hex::encode(repres.unwrap())
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    /// Ensure private keys generate the expected representatives. These tests
    /// are generated from agl/ed25519 to ensure compatibility.
    fn repres_from_privkey_agl() {
        for (i, vector) in ntor_valid_test_vectors().iter().enumerate() {
            let privkey: [u8; 32] = hex::decode(vector[0]).unwrap().try_into().unwrap();
            let true_repres = vector[2];

            let repres_res = representative_from_privkey(&privkey);
            assert!(
                Into::<bool>::into(repres_res.is_some()),
                "failed to get representative when we should have gotten one :("
            );
            let mut repres = repres_res.unwrap();

            repres[31] &= MASK_UNSET_BYTE;
            assert_eq!(
                true_repres,
                hex::encode(repres),
                "[good case] agl/ed25519 ({i}) bad representative from privkey"
            );
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    fn pubkey_from_repres() {
        // testcases from kleshni
        for (i, testcase) in decoding_testcases().iter().enumerate() {
            let repres: [u8; 32] = hex::decode(testcase.representative)
                .unwrap()
                .try_into()
                .unwrap();

            let point = MontgomeryPoint::from_representative(&MontgomeryPoint(repres));
            assert_eq!(
                testcase.point,
                hex::encode(point.to_bytes()),
                "[good case] kleshni ({i}) bad representative from point"
            );
        }

        // testcases from golang agl/ed25519
        for (i, vector) in ntor_valid_test_vectors().iter().enumerate() {
            let true_pubkey = vector[1];
            let repres: [u8; 32] = hex::decode(vector[2]).unwrap().try_into().unwrap();

            // ensure that the representative can be reversed to recover the
            // original public key.
            let pubkey = MontgomeryPoint::from_representative(&MontgomeryPoint(repres));
            assert_eq!(
                true_pubkey,
                hex::encode(pubkey.to_bytes()),
                "[good case] agl/ed25519 ({i}) bad pubkey from true representative"
            );
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    fn non_representable_points() {
        for (i, key) in ntor_invalid_keys().iter().enumerate() {
            let privkey: [u8; 32] = hex::decode(key).unwrap().try_into().unwrap();

            // ensure that the representative can be reversed to recover the
            // original public key.
            let res: Option<[u8; 32]> = representative_from_privkey(&privkey).into();
            assert!(
                res.is_none(),
                "[bad case] agl/ed25519 ({i}) expected None, got Some({})",
                hex::encode(res.unwrap())
            );
        }
    }

    /// returns a set of keypair encodings generated by (a fork of) the golang
    /// implementation agl/ed25519 which is used by the mainstream obfs4
    /// library. Each set of three strings is
    ///
    ///   1) the generated private key scalar
    ///   2) the associated public key point
    ///   3) the successfully created representative
    ///
    /// All of these are valid keypairs and our public key to
    /// representative implementation (and repres-to-pubkey) should match and
    /// handle these cases.
    ///
    fn ntor_valid_test_vectors() -> [[&'static str; 3]; 20] {
        [
            [
                "eec0c0e43a2f693557dac4938c9a0f44be8bf7999399f26a24e5eab3267517c8",
                "309d1f477c62df666f47b87930d1883c072d007a169c03d1c231efe2e51cae1f",
                "bfd7e6dc33b735403cf6c7235513463843db8e1d2c16e62f0d5cacc8a3817515",
            ],
            [
                "d27f87a4850f85ef5211094eb417bc8fb9441dd8eedba8def6fd040da93fdf94",
                "bb6fe9e93c929e104a6b9f956c5de1fdc977899a781d50e76dd8f8852f19e635",
                "420c98e6ac9cabaccf54e02034916df64a45ad1e7799b5d2ab0403073c6f6a21",
            ],
            [
                "54b0d4e7110fb3a6ca5424fa7ffdc7cc599f9280df9759d1eb5d04186a4e82dd",
                "f305e32fbd38dd1e6b04ba32620c6b8db121ed3216f7118875580bd454eb077d",
                "a2b1a54463ad048ea9780fe2f92e0517636d2cd537d77a18cb6be03f1f991c04",
            ],
            [
                "9ce200c8a0c3e617c7c5605dc60d1ce67e30a608c492143d643880f91594a6dd",
                "56a2e451811eb62c78090c3d076f4b179b2e9baa4d80188a3db319301031191b",
                "c16f22f4899aae477d37c250164d10c9c898a820bf790b1532c3bc379b8d733e",
            ],
            [
                "98f09f9dedc813654e4ba28c9cd545587b20c6133603f13d8d4da2b67b4eab8c",
                "210d599d6b8d1659e4a6eb98fdebd1a7024b22ba148af2a603ab807735af6a57",
                "fc4ad471aff8243195ab6778054b0b243f93b4d31d5ac3a5bda9354dc3def735",
            ],
            [
                "fa850ae6663a8c7b84c71c6391e0b02df2d6adbc30a03b961c4b496b9979cf9d",
                "7fc7a4a8ae33cd045b064d1618689a7e16c87ce611f8f519433b10134dc57b04",
                "062d292892515a6a9e71e1430cc593e5cf90e4c18d7c0c0eaae7a07768e6f713",
            ],
            [
                "c19e91e47db473ff36714a8490665eaf6e57d228ef116e7771febce437c9e4ef",
                "5ca47c5affeaeac3d67ef6564f0faa0bd575857eb4e315b57458959b0034f75c",
                "f22ceea9e0e3826a308fe60df0edf4b82177e3704750f7af6e41aa5c5d806f16",
            ],
            [
                "012fb2f110c7da5d56bb86e28e23dff1d860bb6ed11e145be9344ba756dd4e6e",
                "badb58d30c1a8b6bbc0ee97f627272aa1c5625a1cadb7bf75fa274f76c081964",
                "62cf0d3d7c67715a7cc982c9186ccd4d151b64b2cef862433a963b7b2c13f033",
            ],
            [
                "fc9fec244ec6064f1060aabad079d04d1bb180239b07d4d02383ecbb05a7095e",
                "54fe5cc959be48e5a0251026ac4cd0f5a424b8f5c157a7c59857d2ab11521e4c",
                "0326b2e14412ef42fdd0144f96f6b47a5e0954aa110ca7ba124d1aca82269e1f",
            ],
            [
                "1cb297f54fd1b320995f885591abdd5b84ff35f55ed22f85475a00c0c97b648a",
                "2b0472ba2ffd8af768c2b6dab2b6db21c0ca153537d4b3c638a7cf7708c99e2d",
                "08bba17691f09c899bba92f8950dec551065249f77e59d46bf113c56fc54a20f",
            ],
            [
                "4871c2e7ada1911544713cbf15e0553d4972cc9867a4e67a667643b8e7a77d30",
                "d73258438f51a0f603180aa349e3276fd623bcce61ff9d2dbb9fd9a9aaf53e40",
                "a5ad91e362963312d95659b2e97bfcfddca573841f864cf8a8e0e075a72e4d1c",
            ],
            [
                "52959827c6c7d3e3b6b50089db8a9524243ae7cee3f9ad7eff477587683af118",
                "031d982caf72aa660a68d79439cedd0e0c47d09f9b6c90d1a0c322291591616e",
                "8dd9423dcc8d08c951330954c99eb508395ac26a3e6d864df907ad1b23fd6a37",
            ],
            [
                "12c77ad0259120089f5bfb841999e9e17acf71a00ef7891366e3f286c0122790",
                "ce7cb3c1789b119987d36ed73dd40db07099ae9eca8b8ee53f63f610728d7600",
                "8cdcc4d90a94f8148619bc7a32d230e8bbd4416051f53da3ebda320a40904128",
            ],
            [
                "db46139a816b40cc15be3b82cd799f025cfa0817552bf959386e0a264184a419",
                "03778d7eee1973fbe8a45670bc2172a8fbc8e0627cf81ad932f7bbedc1aca177",
                "f3382b89603501ac8a5038aeda9422af88a2557f6a831b20062518733d59382d",
            ],
            // The following key sets have a v_in_sqrt value of 0
            [
                "51a8b03750f4b34922d3588b73a556a09594b7b014d2b7cefa26bb8c5eee6d2e",
                "e8db45df5146d3745eae81e722af5e030a9a999a3e0d588f84514b125029b81b",
                "f859efb4704b0b4c71959b02976de3ea9746f01e5adacddddba10ee08178cd1d",
            ],
            [
                "d5a46dfdf2c66a76c312e83954fc0cf54f75ff14c2d6febfeb08153e34f54cfd",
                "08a6adca98cbee754c3cdb103b5d9f69e61b87c64339947cbbaa1a956df5b745",
                "139b06604063d7942540fbd33de329a2f733c65a89fd68151743896744397c2b",
            ],
            [
                "a06917dc2988e4b51559ab26e25fd920e8fec2f8f2fe0f4c3c725dce06de7867",
                "868603c764dff5f6db6f963237731452c469dfa2c8c5b682cfec85fc38661415",
                "2bdd5f3dcaeefa352f200306be3471ad90a0a0ac4b6abba44230e284a852b813",
            ],
            [
                "7acad18a021a568d2abaf079d046f5eb55e081a32b00d4f6c77f8b8c9afed866",
                "8e0f52904421469a46b2d636b9d17595573071d16ebff280fc88829b5ef8bd4f",
                "abc0de8594713993eab06144fe9b6d7bd04227c62bda19ef984008a93161fb33",
            ],
            [
                "c547b93c519a1c0b40b71fe7b08e13b38639564e9317f6b58c5f99d5ad82471a",
                "687fe9c6fe84e94ef0f7344abdac92dfd60dabc6156c1a3eea19d0d06705b461",
                "8b0ea3b2215bf829aedd250c629557ca646515861aa0b7fc881c50d622f9ac38",
            ],
            [
                "77e48dfa107bbfdda73f50ec2c38347e4fcc9c38866adb75488a2143993a058f",
                "7d124e12af90216f26ce3198f6b02e76faf990dd248cdb246dd80d4e1fef3d4d",
                "128481624af3015c6226428a247514370800f212a7a06c90dfe4f1aa672d3b3e",
            ],
        ]
    }

    /// returns a set of private keys generated by (a fork of) the golang
    /// implementation agl/ed25519 which is used by the mainstream obfs4
    /// library.
    ///
    /// All of these fail to generate a keypair capable of using elligator2
    /// to encode of the public key.
    ///
    #[cfg(feature = "elligator2")]
    fn ntor_invalid_keys() -> [&'static str; 16] {
        [
            "fd0d592d67038a6253331547949d70eb7a6b6c4c4831a1bc235554765b20f845",
            "9576aa473a2b73b174e753ada7d55bc34ae8c05c1b1d6077f9a098984df9cf52",
            "5b26538e0663a453994cf49d5614926786a0549c0123fa9afc7be99e04afc9ea",
            "d4e58db7420267ad43e72e1fe0dee1acb9ca547e258e22370d76c0945f4b1a1e",
            "01b047693c6b5212607387df88d1a427d2f24bd24157058705fc090e22778a64",
            "d2d363fad3ea3aceb8262adc1184f32c6f63911e6bc008c87f366f9c2b60753c",
            "75f703e3095343cf5d3ccd05a3fea06f82509a26c391a0365a1f1ca5e1d5f82f",
            "1f6986c9146f2d4b1907a812e7e7254c82e121776d58fd9c4a5f6741a326e2ef",
            "fe8465f11b40d52dc845df0a1639398b1726409d3b52526082c3e67c52f06842",
            "4546f8e010e0d3be7ab3e97480cecc411b054013960ff4032b3d3e5afe1565e0",
            "fc0f99f041118fd44c685b87b143b48d6d8c820d9f07235eeb7f7a9468dc0ca0",
            "847c1d842a2e91521d1a63e191d3d2389e54c73378130f376d013781730ace3e",
            "7d8a740b09f477588bc9a9020b2444ee384718f889403c02f3a61e69f55e6f7f",
            "0549080985424df8f9401be8802e8c6a4c02737c474ac76c9d3f7968a3fca40a",
            "53cd411b966503129365517e5c1b04e9f52a248cc57599af9ed58c9ff5b774d4",
            "015aebbe87a5e94c5d8d3179583cf46d02af06c8f99a6d4ce8a3a4b1de097cd2",
        ]
    }

    const ENCODING_TESTS_COUNT: usize = 6;
    struct EncodingTestCase {
        high_y: bool,
        point: &'static str,
        representative: Option<&'static str>,
    }

    fn encoding_testcases() -> [EncodingTestCase; ENCODING_TESTS_COUNT] {
        [
            // A not encodable point with both "high_y" values
            EncodingTestCase {
                point: "e6f66fdf6e230c603c5e6e59a254ea1476a13eb9511b9549846781e12e52230a",
                high_y: false,
                representative: None,
            },
            EncodingTestCase {
                point: "e6f66fdf6e230c603c5e6e59a254ea1476a13eb9511b9549846781e12e52230a",
                high_y: true,
                representative: None,
            },
            // An encodable point with both "high_y" values
            EncodingTestCase {
                point: "33951964003c940878063ccfd0348af42150ca16d2646f2c5856e8338377d800",
                high_y: false,
                representative: Some(
                    "999b591b6697d074f266192277d554dec3c24c2ef6108101f63d94f7fff3a013",
                ),
            },
            EncodingTestCase {
                point: "33951964003c940878063ccfd0348af42150ca16d2646f2c5856e8338377d800",
                high_y: true,
                representative: Some(
                    "bd3d2a7ed1c8a100a977f8d992e33aaa6f630d55089770ea469101d7fd73d13d",
                    // "999b591b6697d074f266192277d554dec3c24c2ef6108101f63d94f7fff3a013",
                ),
            },
            // 0 with both "high_y" values
            EncodingTestCase {
                point: "0000000000000000000000000000000000000000000000000000000000000000",
                high_y: false,
                representative: Some(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                ),
            },
            EncodingTestCase {
                point: "0000000000000000000000000000000000000000000000000000000000000000",
                high_y: true,
                representative: Some(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                ),
            },
        ]
    }

    const DECODING_TESTS_COUNT: usize = 7;
    struct DecodingTestCase {
        representative: &'static str,
        point: &'static str,
    }

    fn decoding_testcases() -> [DecodingTestCase; DECODING_TESTS_COUNT] {
        [
            // A small representative with false "high_y" property
            DecodingTestCase {
                representative: "e73507d38bae63992b3f57aac48c0abc14509589288457995a2b4ca3490aa207",
                point: "1e8afffed6bf53fe271ad572473262ded8faec68e5e67ef45ebb82eeba52604f",
            },
            // A small representative with true "high_y" property
            DecodingTestCase {
                representative: "95a16019041dbefed9832048ede11928d90365f24a38aa7aef1b97e23954101b",
                point: "794f05ba3e3a72958022468c88981e0be5782be1e1145ce2c3c6fde16ded5363",
            },
            // The last representative returning true: (p - 1) / 2
            DecodingTestCase {
                representative: "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
                point: "9cdb525555555555555555555555555555555555555555555555555555555555",
            },
            // The first representative returning false: (p + 1) / 2
            DecodingTestCase {
                representative: "f7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
                point: "9cdb525555555555555555555555555555555555555555555555555555555555",
            },
            // A large representative with false "high_y" property
            DecodingTestCase {
                representative: "179f24730ded2ce3173908ec61964653b8027e383f40346c1c9b4d2bdb1db76c",
                point: "10745497d35c6ede6ea6b330546a6fcbf15c903a7be28ae69b1ca14e0bf09b60",
            },
            // A large representative with true "high_y" property
            DecodingTestCase {
                representative: "8a2f286180c3d8630b5f5a3c7cc027a55e0d3ffb3b1b990c5c7bb4c3d1f91b6f",
                point: "6d3187192afc3bcc05a497928816e3e2336dc539aa7fc296a9ee013f560db843",
            },
            // 0
            DecodingTestCase {
                representative: "0000000000000000000000000000000000000000000000000000000000000000",
                point: "0000000000000000000000000000000000000000000000000000000000000000",
            },
        ]
    }
}

