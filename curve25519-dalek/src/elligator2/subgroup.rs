use super::*;
use crate::{MontgomeryPoint, Scalar};

use rand::{thread_rng, Rng};

// #[test]
#[cfg(feature = "elligator2")]
/// Check the first 32 bytes of a server handshake (the server's serialized
/// Elligator public key representative) and return a boolean indicating whether
/// they represent a public key that is off the prime-order subgroup of
/// Curve25519, regardless of whether the representative is interpreted
/// according to pre-v0.0.12 conventions or post-v0.0.12 conventions.
// We don't know whether we are dealing with a pre-v0.0.12 obfs4proxy (which
// uses 255 bits of the representative) or a post-v0.0.12
// obfs4proxy (which uses 254 bits of the representative). Try it both ways,
// and convervatively return True only if the point is off the subgroup in
// both cases.
//
// When bit 254 is 0, these two interpretations are the same, and the
// probability of a random string being off the subgroup is 3/4. When bit 255
// is 1, then the two interpretations each have probability 3/4 of
// being off the subgroup; they are both off the subgroup with probability
// 9/16. Since bit 254 is either 0 or 1 with probability 1/2, the probability
// that a random string represents a point off the subgroup is the average of
// 3/4 and 9/16, or 21/32.
fn subgroup_check() {
    let order = Scalar::from(2u128 ^ 252 + 27742317777372353535851937790883648493).bytes;
    let mut count = 0;
    let iterations = 10;

    let mut i = 0;
    while i < iterations {
        let y_sk = thread_rng().gen::<[u8; 32]>();
        let y_sk_tweak = thread_rng().gen::<u8>();

        let mut y_repr_bytes = match representative_from_privkey(&y_sk, y_sk_tweak) {
            Some(r) => r,
            None => continue,
        };

        println!(
            "{} {:02x}",
            hex::encode(&y_repr_bytes),
            y_repr_bytes[31] & 0b1100_0000
        );

        // Multiply the point by the order of the prime-order subgroup, check if it is the identity.
        y_repr_bytes[31] &= 0b0111_1111;
        let y_repr_255 = MontgomeryPoint::map_to_point(&y_repr_bytes).mul_clamped(order);
        let off_subgroup_255 = FieldElement::from_bytes(&y_repr_255.0);
        let os_255: bool = off_subgroup_255.is_zero().into();

        // Multiply the point by the order of the prime-order subgroup, check if it is the identity.
        y_repr_bytes[31] &= 0b0011_1111;
        let y_repr_254 = MontgomeryPoint::map_to_point(&y_repr_bytes).mul_clamped(order);
        let off_subgroup_254 = FieldElement::from_bytes(&y_repr_254.0);
        let os_254: bool = off_subgroup_254.is_zero().into();

        if !os_254 & !os_255 {
            count += 1;
        }
        i += 1;
    }
    assert_ne!(count, 0);
    assert_ne!(count, iterations);
    /*
    Yr_255 = from_bytes_255(Yrb)
    Y_255 = elligator_dir_map(Yr_255)[0]
    # Multiply the point by the order of the prime-order subgroup, check if it
    # is the identity.
    off_subgroup_255 = Mt.scalarmult(Y_255, Mt.order).to_num() != 0

    Yr_254 = from_bytes_254(Yrb)
    Y_254 = elligator_dir_map(Yr_254)[0]
    off_subgroup_254 = Mt.scalarmult(Y_254, Mt.order).to_num() != 0

    return off_subgroup_255 and off_subgroup_254
    */
}

#[test]
#[cfg(feature = "elligator2")]
/// pubkey_subgroup_check2 tests that Elligator representatives produced by
/// NewKeypair map to public keys that are not always on the prime-order subgroup
/// of Curve25519. (And incidentally that Elligator representatives agree with
/// the public key stored in the Keypair.)
///
/// See discussion under "Step 2" at https://elligator.org/key-exchange.
// We will test the public keys that comes out of NewKeypair by
// multiplying each one by L, the order of the prime-order subgroup of
// Curve25519, then checking the order of the resulting point. The error
// condition we are checking for specifically is output points always
// having order 1, which means that public keys are always on the
// prime-order subgroup of Curve25519, which would make Elligator
// representatives distinguishable from random. More generally, we want
// to ensure that all possible output points of low order are covered.
//
// We have to do some contortions to conform to the interfaces we use.
// We do scalar multiplication by L using Edwards coordinates, rather
// than the Montgomery coordinates output by Keypair.Public and
// Representative.ToPublic, because the Montgomery-based
// crypto/curve25519.X25519 clamps the scalar to be a multiple of 8,
// which would not allow us to use the scalar we need. The Edwards-based
// ScalarMult only accepts scalars that are strictly less than L; we
// work around this by multiplying the point by L - 1, then adding the
// point once to the product.
fn pubkey_subgroup_check2() {
    // This is the same as scMinusOne in filippo.io/edwards25519.
    // https://github.com/FiloSottile/edwards25519/blob/v1.0.0/scalar.go#L34

    let scalar_order_minus1 = Scalar::from_canonical_bytes([
        236_u8, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16,
    ])
    .unwrap();

    // Returns a new edwards25519.Point that is v multiplied by the subgroup order.
    let scalar_mult_order = |v: &EdwardsPoint| -> EdwardsPoint {
        // v * (L - 1) + v => v * L
        let p = &scalar_order_minus1 * v;
        &p + v
    };

    // Generates a new Keypair using, and returns the public key representative
    // along, with its public key as a newly allocated edwards25519.Point.
    let generate = || -> ([u8; 32], EdwardsPoint) {
        for _ in 0..63 {
            let y_sk = thread_rng().gen::<[u8; 32]>();
            let y_sk_tweak = thread_rng().gen::<u8>();
            let y_repr_bytes = match representative_from_privkey(&y_sk, y_sk_tweak) {
                Some(r) => r,
                None => continue,
            };
            let y_pk = EdwardsPoint::mul_base_clamped(y_sk);
            return (y_repr_bytes, y_pk);
        }
        panic!("failed ot generate a valid keypair");
    };

    // These are all the points of low order that may result from
    // multiplying an Elligator-mapped point by L. We will test that all of
    // them are covered.
    let low_order_points = [
        "0100000000000000000000000000000000000000000000000000000000000000",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000080",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa",
    ];
    let mut counts = [0; 8];

    // Assuming a uniform distribution of representatives, the probability
    // that a specific low-order point will not be covered after n trials is
    // (7/8)^n. The probability that *any* of the 8 low-order points will
    // remain uncovered after n trials is at most 8 times that, 8*(7/8)^n.
    // We must do at least log((1e-12)/8)/log(7/8) = 222.50 trials, in the
    // worst case, to ensure a false error rate of less than 1 in a
    // trillion. In practice, we keep track of the number of covered points
    // and break the loop when it reaches 8, so when representatives are
    // actually uniform we will usually run much fewer iterations.
    let mut num_covered = 0;
    for _ in 0..255 {
        let (repr, pk) = generate();
        let v = scalar_mult_order(&pk);

        let b = v.to_montgomery().to_bytes();
        let b_str = hex::encode(&b);
        let index = match low_order_points.iter().position(|x| x == &b_str) {
            Some(idx) => idx,
            None => {
                panic!(
                    "map({})*order yielded unexpected point {:}",
                    hex::encode(repr),
                    b_str
                );
            }
        };

        counts[index] += 1;
        if counts[index] == 1 {
            // We just covered a new point for the first time.
            num_covered += 1;
            if num_covered == low_order_points.len() {
                break;
            }
        }
    }
    let mut failed = false;
    for (i, count) in counts.iter().enumerate() {
        println!("{} {}", low_order_points[i], count);
        if *count == 0 {
            failed = true;
        }
    }

    if failed {
        panic!("not all low order points were covered")
    }
}

#[test]
#[cfg(feature = "elligator2")]
fn pubkey_subgroup_check3() {
    // This is the same as scMinusOne in filippo.io/edwards25519.
    // https://github.com/FiloSottile/edwards25519/blob/v1.0.0/scalar.go#L34
    let scalar_order_minus1 = Scalar::from_canonical_bytes([
        236_u8, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16,
    ])
    .unwrap();

    // Returns a new edwards25519.Point that is v multiplied by the subgroup order.
    let scalar_mult_order = |v: &EdwardsPoint| -> EdwardsPoint {
        // v * (L - 1) + v => v * L
        let p = &scalar_order_minus1 * v;
        &p + v
    };

    // Generates a new Keypair using, and returns the public key representative
    // along, with its public key as a newly allocated edwards25519.Point.
    let generate = || -> ([u8; 32], EdwardsPoint) {
        for _ in 0..63 {
            let y_sk = thread_rng().gen::<[u8; 32]>();
            let y_sk_tweak = thread_rng().gen::<u8>();

            let y_repr_bytes = match representative_from_privkey(&y_sk, y_sk_tweak) {
                Some(r) => r,
                None => continue,
            };
            let y_pk: EdwardsPoint = match EdwardsPoint::mul_base_clamped_dirty(y_sk).into() {
                Some(p) => p,
                None => continue,
            };

            assert_eq!(MontgomeryPoint::map_to_point(&y_repr_bytes), y_pk.to_montgomery());

            // let fe = FieldElement::from_bytes(&y_pk.to_montgomery().to_bytes());
            // let y_repr_bytes = match representative_from_pubkey(&fe, y_sk_tweak) {
            //     Some(r) => r,
            //     None => continue,
            // };

            return (y_repr_bytes, y_pk);
        }
        panic!("failed to generate a valid keypair");
    };

    // These are all the points of low order that may result from
    // multiplying an Elligator-mapped point by L. We will test that all of
    // them are covered.
    let low_order_points = [
        "0100000000000000000000000000000000000000000000000000000000000000",
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000080",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
        "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
        "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa",
    ];
    let mut counts = [0; 8];

    // Assuming a uniform distribution of representatives, the probability
    // that a specific low-order point will not be covered after n trials is
    // (7/8)^n. The probability that *any* of the 8 low-order points will
    // remain uncovered after n trials is at most 8 times that, 8*(7/8)^n.
    // We must do at least log((1e-12)/8)/log(7/8) = 222.50 trials, in the
    // worst case, to ensure a false error rate of less than 1 in a
    // trillion. In practice, we keep track of the number of covered points
    // and break the loop when it reaches 8, so when representatives are
    // actually uniform we will usually run much fewer iterations.
    let mut num_covered = 0;
    for _ in 0..255 {
        let (repr, pk) = generate();
        let v = scalar_mult_order(&pk);

        let b = v.to_montgomery().to_bytes();
        let b_str = hex::encode(&b);
        let index = match low_order_points.iter().position(|x| x == &b_str) {
            Some(idx) => idx,
            None => {
                panic!(
                    "map({})*order yielded unexpected point {:}",
                    hex::encode(repr),
                    b_str
                );
            }
        };

        counts[index] += 1;
        if counts[index] == 1 {
            // We just covered a new point for the first time.
            num_covered += 1;
            if num_covered == low_order_points.len() {
                break;
            }
        }
    }
    let mut failed = false;
    for (i, count) in counts.iter().enumerate() {
        println!("{} {}", low_order_points[i], count);
        if *count == 0 {
            failed = true;
        }
    }

    if failed {
        panic!("not all low order points were covered")
    }
}
