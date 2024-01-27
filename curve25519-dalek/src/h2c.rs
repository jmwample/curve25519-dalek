
// ------------------------------------------------------------------------
// RfC 9380 Tests
//
// Each test vector in this section lists values computed by the
// appropriate encoding function, with variable names defined as in
// RFC9380 Section 3. For example, for a suite whose encoding type is random
// oracle, the test vector gives the value for msg, u, Q0, Q1, and the
// output point P.
//
//
// * encode_to_curve is a nonuniform encoding from byte strings to
//   points in G.  That is, the distribution of its output is not
//   uniformly random in G: the set of possible outputs of
//   encode_to_curve is only a fraction of the points in G, and some
//   points in this set are more likely to be output than others.
//   Section 10.4 gives a more precise definition of encode_to_curve's
//   output distribution.
//
//       encode_to_curve(msg)
//
//       Input: msg, an arbitrary-length byte string.
//       Output: P, a point in G.
//
//       Steps:
//       1. u = hash_to_field(msg, 1)
//       2. Q = map_to_curve(u[0])
//       3. P = clear_cofactor(Q)
//       4. return P
//
//
// * hash_to_curve is a uniform encoding from byte strings to points in
//   G.  That is, the distribution of its output is statistically close
//   to uniform in G.
//
//   This function is suitable for most applications requiring a random
//   oracle returning points in G, when instantiated with any of the
//   map_to_curve functions described in Section 6.  See Section 10.1
//   for further discussion.
//
//       hash_to_curve(msg)
//
//       Input: msg, an arbitrary-length byte string.
//       Output: P, a point in G.
//
//       Steps:
//       1. u = hash_to_field(msg, 2)
//       2. Q0 = map_to_curve(u[0])
//       3. Q1 = map_to_curve(u[1])
//       4. R = Q0 + Q1              # Point addition
//       5. P = clear_cofactor(R)
//       6. return P
// ------------------------------------------------------------------------
#[cfg(feature="digest")]
#[cfg(test)]
mod rfc9380 {
    use crate::{MontgomeryPoint, field::FieldElement};
    use crate::elligator2::map_to_point_new;
    use crate::scalar::Scalar;

    use sha2::{Sha512, Digest};
    use subtle::{Choice, ConstantTimeEq};
    use hex::FromHex;


    pub(crate) const H_EFF: Scalar = Scalar{
            bytes: [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    };

    /// Input:
    ///     * out -> reference to a list of FieldElements of length count such
    ///     that all resulting Field Elements can be written returned.
    ///     (u_0, ..., u_(count - 1)), a list of field elements.
    ///
    ///     * msg -> message to be processed
    ///
    ///     * count -> number of output points
    ///
    /// Output:
    ///     * Choice -> 1 for success, 0 for failure
    ///
    fn hash_to_field(out: &mut [FieldElement], msg: impl AsRef<[u8]>, count: usize) -> Choice {
        let result = count.ct_eq(&out.len());

        let bytes = msg.as_ref();
        let mut hash = Sha512::new();
        hash.update(bytes);
        let h = hash.finalize();
        let mut res = [0u8; 32];
        res.copy_from_slice(&h[..32]);

        // let sign_bit = (res[31] & 0x80) >> 7;
        println!("{}", hex::encode(&res));
        Choice::from(result)
    }


    /// Clear the cofactor associated with the
    ///
    fn clear_cofactor(x: FieldElement, y: FieldElement) -> [[u8;32]; 2] {
        let x_m = MontgomeryPoint(x.as_bytes());
        let y_m = MontgomeryPoint(y.as_bytes());
        [(&x_m * &H_EFF).to_bytes(), (&y_m * &H_EFF).to_bytes()]
    }

    // ---

    #[allow(unused)]
    fn encode_to_curve(msg: impl AsRef<[u8]>) -> [[u8;32]; 2] {
        let mut field_points = [FieldElement::from_bytes(&[0_u8;32]); 1];
        hash_to_field(&mut field_points, msg, 1);

        let (q_x, q_y) = map_to_curve(&field_points[0].as_bytes());

        clear_cofactor(q_x, q_y)
    }

    fn hash_to_curve(msg: impl AsRef<[u8]>) -> [[u8;32]; 2] {
        let mut field_points = [FieldElement::from_bytes(&[0_u8;32]); 2];
        hash_to_field(&mut field_points, msg, 2);

        let (q0_x, q0_y) = map_to_curve(&field_points[0].as_bytes());
        let (q1_x, q1_y) = map_to_curve(&field_points[1].as_bytes());

        let r_x = &q0_x + &q1_x;
        let r_y = &q0_y + &q1_y;

        clear_cofactor(r_x, r_y)
    }

    /// calculates a point on the elliptic curve E from an element of the finite
    /// field F over which E is defined. Section 6 describes mappings for a
    /// range of curve families.
    ///
    /// The input u and outputs x and y are elements of the field F.  The
    /// affine coordinates (x, y) specify a point on an elliptic curve
    /// defined over F.  Note, however, that the point (x, y) is not a
    /// uniformly random point.
    ///
    /// Input:
    ///     * u -> an element of field F.
    ///
    /// Output:
    ///     * Q - a point on the elliptic curve E.
    ///
    fn map_to_curve(u: &[u8;32]) -> (FieldElement, FieldElement) {
        map_to_point_new(&FieldElement::from_bytes(&u))
    }


    #[test]
    fn map_to_curve_test() {
        for i in 0..CURVE25519_ELL2.len() {
            let testcase = &CURVE25519_ELL2[i];

            let u = testcase[0].must_from_be();
            let mut clamped = u.clone();
            clamped[31] &= 63;

            // map point to curve
            let (q_x, _) = map_to_curve(&clamped);

            // check resulting point
            assert_eq!(q_x.encode_be(), testcase[1], "({i}) incorrect x curve25519 ELL2\n");
        }

        for i in 0..curve25519_XMD_SHA512_ELL2_NU.len() {
            let testcase = &curve25519_XMD_SHA512_ELL2_NU[i];
            let u = testcase.u_0.must_from_le();

            // map point to curve
            let (q_x, q_y) = map_to_curve(&u);

            // check resulting point
            assert_eq!(q_x.encode_le(), testcase.Q_x, "({i}) incorrect Q0_x curve25519 NU\n{:?}", testcase);
            assert_eq!(q_y.encode_le(), testcase.Q_y, "({i}) incorrect Q0_y curve25519 NU\n{:?}", testcase);
        }
        for i in 0..curve25519_XMD_SHA512_ELL2_RO.len() {
            let testcase = &curve25519_XMD_SHA512_ELL2_RO[i];
            let u0 = testcase.u_0.must_from_le();
            let u1 = testcase.u_1.must_from_le();

            // map points to curve
            let (q0_x, q0_y) = map_to_curve(&u0);
            let (q1_x, q1_y) = map_to_curve(&u1);

            // check resulting points
            assert_eq!(q0_x.encode_le(), testcase.Q0_x, "({i}) incorrect Q0_x curve25519 RO\n{:?}", testcase);
            assert_eq!(q0_y.encode_le(), testcase.Q0_y, "({i}) incorrect Q0_y curve25519 RO\n{:?}", testcase);
            assert_eq!(q1_x.encode_le(), testcase.Q1_x, "({i}) incorrect Q1_x curve25519 RO\n{:?}", testcase);
            assert_eq!(q1_y.encode_le(), testcase.Q1_y, "({i}) incorrect Q1_y curve25519 RO\n{:?}", testcase);
        }
    }

    #[test]
    fn curve25519_ro() {
        for i in 0..curve25519_XMD_SHA512_ELL2_RO.len() {
            let testcase = &curve25519_XMD_SHA512_ELL2_RO[i];

            // hash to curve for sha512
            let mut field_points = [FieldElement::from_bytes(&[0_u8;32]); 2];
            let ok: bool = hash_to_field(&mut field_points, testcase.msg, 2).into();
            assert!(ok);
            assert_eq!(hex::encode(field_points[0].as_bytes()), testcase.u_0, "({i}) incorrect hash for curve25519 RO");
            assert_eq!(hex::encode(field_points[1].as_bytes()), testcase.u_0, "({i}) incorrect hash for curve25519 RO");

            // let sign_bit = (res[31] & 0x80) >> 7;

            // map point(s) to curve
            let (q0_x, q0_y) = map_to_point_new(&field_points[0]);
            let (q1_x, q1_y) = map_to_point_new(&field_points[1]);
            assert_eq!(hex::encode(q0_x.as_bytes()), testcase.Q0_x, "({i}) incorrect curve point curve25519 RO");
            assert_eq!(hex::encode(q0_y.as_bytes()), testcase.Q0_y, "({i}) incorrect curve point curve25519 RO");
            assert_eq!(hex::encode(q1_x.as_bytes()), testcase.Q1_x, "({i}) incorrect curve point curve25519 RO");
            assert_eq!(hex::encode(q1_y.as_bytes()), testcase.Q1_y, "({i}) incorrect curve point curve25519 RO");

            // clear cofactor for points
            let p = clear_cofactor(&q0_x + &q1_x, &q0_y + &q1_y);
            assert_eq!(hex::encode(p[0]), testcase.P_x, "({i}) cofactor cleared incorrectly curve25519 RO");
            assert_eq!(hex::encode(p[1]), testcase.P_y, "({i}) cofactor cleared incorrectly curve25519 RO");

            // end to end for RO using hash_to_curve
            let p = hash_to_curve(testcase.msg);
            assert_eq!(hex::encode(p[0]), testcase.P_x, "({i}) end to end incorrect X curve25519 NU");
            assert_eq!(hex::encode(p[1]), testcase.P_y, "({i}) end to end incorrect Y curve25519 NU");
        }
    }

    #[test]
    fn curve25519_nu() {
        for i in 0..curve25519_XMD_SHA512_ELL2_NU.len() {
            let testcase = &curve25519_XMD_SHA512_ELL2_NU[i];

            // hash to curve for sha512
            let mut field_points = [FieldElement::from_bytes(&[0_u8;32]); 1];
            let ok: bool = hash_to_field(&mut field_points, testcase.msg, 1).into();
            assert!(ok);
            assert_eq!(hex::encode(field_points[0].as_bytes()), testcase.u_0, "({i}) incorrect hash for curve25519 NU");

            // let sign_bit = (res[31] & 0x80) >> 7;

            // map point(s) to curve
            let (q0_x, q0_y) = map_to_point_new(&field_points[0]);
            assert_eq!(hex::encode(q0_x.as_bytes()), testcase.Q_x, "({i}) incorrect curve point curve25519 NU");
            assert_eq!(hex::encode(q0_y.as_bytes()), testcase.Q_y, "({i}) incorrect curve point curve25519 NU");

            // clear cofactor for points
            let p0 = clear_cofactor(q0_x, q0_y);

            assert_eq!(hex::encode(p0[0]), testcase.P_x, "({i}) cofactor cleared incorrectly curve25519 NU");
            assert_eq!(hex::encode(p0[1]), testcase.P_y, "({i}) cofactor cleared incorrectly curve25519 NU");

            // end to end for RO using hash_to_curve
            let p = hash_to_curve(testcase.msg);
            assert_eq!(hex::encode(p[0]), testcase.P_x, "({i}) end to end incorrect X curve25519 NU");
            assert_eq!(hex::encode(p[1]), testcase.P_y, "({i}) end to end incorrect Y curve25519 NU");
        }
    }

    #[test]
    fn edwards25519_ro() {
        for i in 0..edwards25519_XMD_SHA512_ELL2_RO.len() {
            let testcase = &edwards25519_XMD_SHA512_ELL2_RO[i];

            let u0: [u8;32] = hex::decode(testcase.u_0).unwrap().try_into().unwrap();
            let u1: [u8;32] = hex::decode(testcase.u_1).unwrap().try_into().unwrap();

            let (x, y) = map_to_curve(&u0);
            assert_eq!(hex::encode(x.as_bytes()), testcase.Q0_x, "({i}) ");
            assert_eq!(hex::encode(y.as_bytes()), testcase.Q0_y, "({i}) ");

            let (x, y) = map_to_curve(&u1);
            assert_eq!(hex::encode(x.as_bytes()), testcase.Q1_x, "({i}) ");
            assert_eq!(hex::encode(y.as_bytes()), testcase.Q1_y, "({i}) ");
        }
    }

    #[test]
    fn edwards25519_nu() {
        for i in 0..edwards25519_XMD_SHA512_ELL2_NU.len() {
            let testcase = &edwards25519_XMD_SHA512_ELL2_NU[i];

            let p: [u8;32] = hex::decode(testcase.P_x).unwrap().try_into().unwrap();

            let (x, y) = map_to_curve(&p);
            assert_eq!(hex::encode(x.as_bytes()), testcase.Q_x, "({i}) ");
            assert_eq!(hex::encode(y.as_bytes()), testcase.Q_y, "({i}) ");
        }
    }

    const CURVE25519_ELL2: [[&'static str;2]; 14] = [
        [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "0000000000000000000000000000000000000000000000000000000000000040",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "0000000000000000000000000000000000000000000000000000000000000080",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "00000000000000000000000000000000000000000000000000000000000000c0",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "673a505e107189ee54ca93310ac42e4545e9e59050aaac6f8b5f64295c8ec02f",
            "242ae39ef158ed60f20b89396d7d7eef5374aba15dc312a6aea6d1e57cacf85e",
        ],
        [
            "922688fa428d42bc1fa8806998fbc5959ae801817e85a42a45e8ec25a0d7545a",
            "696f341266c64bcfa7afa834f8c34b2730be11c932e08474d1a22f26ed82410b",
        ],
        [
            "0d3b0eb88b74ed13d5f6a130e03c4ad607817057dc227152827c0506a538bbba",
            "0b00df174d9fb0b6ee584d2cf05613130bad18875268c38b377e86dfefef177f",
        ],
        [
            "01a3ea5658f4e00622eeacf724e0bd82068992fae66ed2b04a8599be16662ef5",
            "7ae4c58bc647b5646c9f5ae4c2554ccbf7c6e428e7b242a574a5a9c293c21f7e",
        ],
        [
            "69599ab5a829c3e9515128d368da7354a8b69fcee4e34d0a668b783b6cae550f",
            "09024abaaef243e3b69366397e8dfc1fdc14a0ecc7cf497cbe4f328839acce69",
        ],
        [
            "9172922f96d2fa41ea0daf961857056f1656ab8406db80eaeae76af58f8c9f50",
            "beab745a2a4b4e7f1a7335c3ffcdbd85139f3a72b667a01ee3e3ae0e530b3372",
        ],
        [
            "6850a20ac5b6d2fa7af7042ad5be234d3311b9fb303753dd2b610bd566983281",
            "1287388eb2beeff706edb9cf4fcfdd35757f22541b61528570b86e8915be1530",
        ],
        [
            "84417826c0e80af7cb25a73af1ba87594ff7048a26248b5757e52f2824e068f1",
            "51acd2e8910e7d28b4993db7e97e2b995005f26736f60dcdde94bdf8cb542251",
        ],
        [
            "b0fbe152849f49034d2fa00ccc7b960fad7b30b6c4f9f2713eb01c147146ad31",
            "98508bb3590886af3be523b61c3d0ce6490bb8b27029878caec57e4c750f993d",
        ],
        [
            "a0ca9ff75afae65598630b3b93560834c7f4dd29a557aa29c7becd49aeef3753",
            "3c5fad0516bb8ec53da1c16e910c23f792b971c7e2a0ee57d57c32e3655a646b",
        ],
    ];

    // J.4.1.  curve25519_XMD:SHA-512_ELL2_RO_
    //
    // Random Oracle Curve25519 SHA512 Elligator2
    //
    // suite   = curve25519_XMD:SHA-512_ELL2_RO_
    // dst     = QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_RO_
    //
    #[allow(non_upper_case_globals)]
    const curve25519_XMD_SHA512_ELL2_RO: [xmd_sha512_25519_ro_testcase; 5] = [
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[1],
            P_x: "2b4419f1f2d48f5872de692b0aca72cc7b0a60915dd70bde432e826b6abc526d",
            P_y: "1b8235f255a268f0a6fa8763e97eb3d22d149343d495da1160eff9703f2d07dd",
            u_0: "49bed021c7a3748f09fa8cdfcac044089f7829d3531066ac9e74e0994e05bc7d",
            u_1: "5c36525b663e63389d886105cee7ed712325d5a97e60e140aba7e2ce5ae851b6",
            Q0_x: "16b3d86e056b7970fa00165f6f48d90b619ad618791661b7b5e1ec78be10eac1",
            Q0_y: "4ab256422d84c5120b278cbdfc4e1facc5baadffeccecf8ee9bf3946106d50ca",
            Q1_x: "7ec29ddbf34539c40adfa98fcb39ec36368f47f30e8f888cc7e86f4d46e0c264",
            Q1_y: "10d1abc1cae2d34c06e247f2141ba897657fb39f1080d54f09ce0af128067c74",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[2],
            P_x: "68ca1ea5a6acf4e9956daa101709b1eee6c1bb0df1de3b90d4602382a104c036",
            P_y: "2a375b656207123d10766e68b938b1812a4a6625ff83cb8d5e86f58a4be08353",
            u_0: "6412b7485ba26d3d1b6c290a8e1435b2959f03721874939b21782df17323d160",
            u_1: "24c7b46c1c6d9a21d32f5707be1380ab82db1054fde82865d5c9e3d968f287b2",
            Q0_x: "71de3dadfe268872326c35ac512164850860567aea0e7325e6b91a98f86533ad",
            Q0_y: "26a08b6e9a18084c56f2147bf515414b9b63f1522e1b6c5649f7d4b0324296ec",
            Q1_x: "5704069021f61e41779e2ba6b932268316d6d2a6f064f997a22fef16d1eaeaca",
            Q1_y: "50483c7540f64fb4497619c050f2c7fe55454ec0f0e79870bb44302e34232210",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[3],
            P_x: "096e9c8bae6c06b554c1ee69383bb0e82267e064236b3a30608d4ed20b73ac5a",
            P_y: "1eb5a62612cafb32b16c3329794645b5b948d9f8ffe501d4e26b073fef6de355",
            u_0: "5e123990f11bbb5586613ffabdb58d47f64bb5f2fa115f8ea8df0188e0c9e1b5",
            u_1: "5e8553eb00438a0bb1e7faa59dec6d8087f9c8011e5fb8ed9df31cb6c0d4ac19",
            Q0_x: "7a94d45a198fb5daa381f45f2619ab279744efdd8bd8ed587fc5b65d6cea1df0",
            Q0_y: "67d44f85d376e64bb7d713585230cdbfafc8e2676f7568e0b6ee59361116a6e1",
            Q1_x: "30506fb7a32136694abd61b6113770270debe593027a968a01f271e146e60c18",
            Q1_y: "7eeee0e706b40c6b5174e551426a67f975ad5a977ee2f01e8e20a6d612458c3b",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[4],
            P_x: "1bc61845a138e912f047b5e70ba9606ba2a447a4dade024c8ef3dd42b7bbc5fe",
            P_y: "623d05e47b70e25f7f1d51dda6d7c23c9a18ce015fe3548df596ea9e38c69bf1",
            u_0: "20f481e85da7a3bf60ac0fb11ed1d0558fc6f941b3ac5469aa8b56ec883d6d7d",
            u_1: "017d57fd257e9a78913999a23b52ca988157a81b09c5442501d07fed20869465",
            Q0_x: "02d606e2699b918ee36f2818f2bc5013e437e673c9f9b9cdc15fd0c5ee913970",
            Q0_y: "29e9dc92297231ef211245db9e31767996c5625dfbf92e1c8107ef887365de1e",
            Q1_x: "38920e9b988d1ab7449c0fa9a6058192c0c797bb3d42ac345724341a1aa98745",
            Q1_y: "24dcc1be7c4d591d307e89049fd2ed30aae8911245a9d8554bf6032e5aa40d3d",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[0],
            P_x: "2de3780abb67e861289f5749d16d3e217ffa722192d16bbd9d1bfb9d112b98c0",
            P_y: "3b5dc2a498941a1033d176567d457845637554a2fe7a3507d21abd1c1bd6e878",
            u_0: "005fe8a7b8fef0a16c105e6cadf5a6740b3365e18692a9c05bfbb4d97f645a6a",
            u_1: "1347edbec6a2b5d8c02e058819819bee177077c9d10a4ce165aab0fd0252261a",
            Q0_x: "36b4df0c864c64707cbf6cf36e9ee2c09a6cb93b28313c169be29561bb904f98",
            Q0_y: "6cd59d664fb58c66c892883cd0eb792e52055284dac3907dd756b45d15c3983d",
            Q1_x: "3fa114783a505c0b2b2fbeef0102853c0b494e7757f2a089d0daae7ed9a0db2b",
            Q1_y: "76c0fe7fec932aaafb8eefb42d9cbb32eb931158f469ff3050af15cfdbbeff94",
        },
    ];

    // J.4.2.  curve25519_XMD:SHA-512_ELL2_NU_
    //
    // Nonuniform Encoding Curve25519 SHA512 Elligator2
    //
    //    suite: curve25519_XMD:SHA-512_ELL2_NU_
    //    dst: QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_NU_
    //
    #[allow(non_upper_case_globals)]
    const curve25519_XMD_SHA512_ELL2_NU: [xmd_sha512_25519_nu_testcase; 5] = [
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[0],
            P_x: "1bb913f0c9daefa0b3375378ffa534bda5526c97391952a7789eb976edfe4d08",
            P_y: "4548368f4f983243e747b62a600840ae7c1dab5c723991f85d3a9768479f3ec4",
            u_0: "608d892b641f0328523802a6603427c26e55e6f27e71a91a478148d45b5093cd",
            Q_x: "51125222da5e763d97f3c10fcc92ea6860b9ccbbd2eb1285728f566721c1e65b",
            Q_y: "343d2204f812d3dfc5304a5808c6c0d81a903a5d228b342442aa3c9ba5520a3d",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[1],
            P_x: "7c22950b7d900fa866334262fcaea47a441a578df43b894b4625c9b450f9a026",
            P_y: "5547bc00e4c09685dcbc6cb6765288b386d8bdcb595fa5a6e3969e08097f0541",
            u_0: "46f5b22494bfeaa7f232cc8d054be68561af50230234d7d1d63d1d9abeca8da5",
            Q_x: "7d56d1e08cb0ccb92baf069c18c49bb5a0dcd927eff8dcf75ca921ef7f3e6eeb",
            Q_y: "404d9a7dc25c9c05c44ab9a94590e7c3fe2dcec74533a0b24b188a5d5dacf429",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[2],
            P_x: "31ad08a8b0deeb2a4d8b0206ca25f567ab4e042746f792f4b7973f3ae2096c52",
            P_y: "405070c28e78b4fa269427c82827261991b9718bd6c6e95d627d701a53c30db1",
            u_0: "235fe40c443766ce7e18111c33862d66c3b33267efa50d50f9e8e5d252a40aaa",
            Q_x: "3fbe66b9c9883d79e8407150e7c2a1c8680bee496c62fabe4619a72b3cabe90f",
            Q_y: "08ec476147c9a0a3ff312d303dbbd076abb7551e5fce82b48ab14b433f8d0a7b",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[3],
            P_x: "027877759d155b1997d0d84683a313eb78bdb493271d935b622900459d52ceaa",
            P_y: "54d691731a53baa30707f4a87121d5169fb5d587d70fb0292b5830dedbec4c18",
            u_0: "001e92a544463bda9bd04ddbe3d6eed248f82de32f522669efc5ddce95f46f5b",
            Q_x: "227e0bb89de700385d19ec40e857db6e6a3e634b1c32962f370d26f84ff19683",
            Q_y: "5f86ff3851d262727326a32c1bf7655a03665830fa7f1b8b1e5a09d85bc66e4a",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[4],
            P_x: "5fd892c0958d1a75f54c3182a18d286efab784e774d1e017ba2fb252998b5dc1",
            P_y: "750af3c66101737423a4519ac792fb93337bd74ee751f19da4cf1e94f4d6d0b8",
            u_0: "1a68a1af9f663592291af987203393f707305c7bac9c8d63d6a729bdc553dc19",
            Q_x: "3bcd651ee54d5f7b6013898aab251ee8ecc0688166fce6e9548d38472f6bd196",
            Q_y: "1bb36ad9197299f111b4ef21271c41f4b7ecf5543db8bb5931307ebdb2eaa465",
        },
    ];

    // J.5.1.  edwards25519_XMD:SHA-512_ELL2_RO_
    //
    // Random Oracle Edwards 25519 SHA512 Elligator2
    //
    //    suite: edwards25519_XMD:SHA-512_ELL2_RO_
    //    dst: QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_RO_
    //
    #[allow(non_upper_case_globals)]
    const edwards25519_XMD_SHA512_ELL2_RO: [xmd_sha512_25519_ro_testcase; 5] = [
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[0],
            P_x: "3c3da6925a3c3c268448dcabb47ccde5439559d9599646a8260e47b1e4822fc6",
            P_y: "09a6c8561a0b22bef63124c588ce4c62ea83a3c899763af26d795302e115dc21",
            u_0: "03fef4813c8cb5f98c6eef88fae174e6e7d5380de2b007799ac7ee712d203f3a",
            u_1: "780bdddd137290c8f589dc687795aafae35f6b674668d92bf92ae793e6a60c75",
            Q0_x: "6549118f65bb617b9e8b438decedc73c496eaed496806d3b2eb9ee60b88e09a7",
            Q0_y: "7315bcc8cf47ed68048d22bad602c6680b3382a08c7c5d3f439a973fb4cf9feb",
            Q1_x: "31dcfc5c58aa1bee6e760bf78cbe71c2bead8cebb2e397ece0f37a3da19c9ed2",
            Q1_y: "7876d81474828d8a5928b50c82420b2bd0898d819e9550c5c82c39fc9bafa196",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[1],
            P_x: "608040b42285cc0d72cbb3985c6b04c935370c7361f4b7fbdb1ae7f8c1a8ecad",
            P_y: "1a8395b88338f22e435bbd301183e7f20a5f9de643f11882fb237f88268a5531",
            u_0: "5081955c4141e4e7d02ec0e36becffaa1934df4d7a270f70679c78f9bd57c227",
            u_1: "005bdc17a9b378b6272573a31b04361f21c371b256252ae5463119aa0b925b76",
            Q0_x: "5c1525bd5d4b4e034512949d187c39d48e8cd84242aa4758956e4adc7d445573",
            Q0_y: "2bf426cf7122d1a90abc7f2d108befc2ef415ce8c2d09695a7407240faa01f29",
            Q1_x: "37b03bba828860c6b459ddad476c83e0f9285787a269df2156219b7e5c86210c",
            Q1_y: "285ebf5412f84d0ad7bb4e136729a9ffd2195d5b8e73c0dc85110ce06958f432",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[2],
            P_x: "6d7fabf47a2dc03fe7d47f7dddd21082c5fb8f86743cd020f3fb147d57161472",
            P_y: "53060a3d140e7fbcda641ed3cf42c88a75411e648a1add71217f70ea8ec561a6",
            u_0: "285ebaa3be701b79871bcb6e225ecc9b0b32dff2d60424b4c50642636a78d5b3",
            u_1: "2e253e6a0ef658fedb8e4bd6a62d1544fd6547922acb3598ec6b369760b81b31",
            Q0_x: "3ac463dd7fddb773b069c5b2b01c0f6b340638f54ee3bd92d452fcec3015b52d",
            Q0_y: "7b03ba1e8db9ec0b390d5c90168a6a0b7107156c994c674b61fe696cbeb46baf",
            Q1_x: "0757e7e904f5e86d2d2f4acf7e01c63827fde2d363985aa7432106f1b3a444ec",
            Q1_y: "50026c96930a24961e9d86aa91ea1465398ff8e42015e2ec1fa397d416f6a1c0",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[3],
            P_x: "5fb0b92acedd16f3bcb0ef83f5c7b7a9466b5f1e0d8d217421878ea3686f8524",
            P_y: "2eca15e355fcfa39d2982f67ddb0eea138e2994f5956ed37b7f72eea5e89d2f7",
            u_0: "4fedd25431c41f2a606952e2945ef5e3ac905a42cf64b8b4d4a83c533bf321af",
            u_1: "02f20716a5801b843987097a8276b6d869295b2e11253751ca72c109d37485a9",
            Q0_x: "703e69787ea7524541933edf41f94010a201cc841c1cce60205ec38513458872",
            Q0_y: "32bb192c4f89106466f0874f5fd56a0d6b6f101cb714777983336c159a9bec75",
            Q1_x: "0c9077c5c31720ed9413abe59bf49ce768506128d810cb882435aa90f713ef6b",
            Q1_y: "7d5aec5210db638c53f050597964b74d6dda4be5b54fa73041bf909ccb3826cb",
        },
        xmd_sha512_25519_ro_testcase {
            msg: RFC9380_TEST_MESSAGES[4],
            P_x: "0efcfde5898a839b00997fbe40d2ebe950bc81181afbd5cd6b9618aa336c1e8c",
            P_y: "6dc2fc04f266c5c27f236a80b14f92ccd051ef1ff027f26a07f8c0f327d8f995",
            u_0: "6e34e04a5106e9bd59f64aba49601bf09d23b27f7b594e56d5de06df4a4ea33b",
            u_1: "1c1c2cb59fc053f44b86c5d5eb8c1954b64976d0302d3729ff66e84068f5fd96",
            Q0_x: "21091b2e3f9258c7dfa075e7ae513325a94a3d8a28e1b1cb3b5b6f5d65675592",
            Q0_y: "41a33d324c89f570e0682cdf7bdb78852295daf8084c669f2cc9692896ab5026",
            Q1_x: "4c07ec48c373e39a23bd7954f9e9b66eeab9e5ee1279b867b3d5315aa815454f",
            Q1_y: "67ccac7c3cb8d1381242d8d6585c57eabaddbb5dca5243a68a8aeb5477d94b3a",
        },
    ];

    // J.5.2.  edwards25519_XMD:SHA-512_ELL2_NU_
    //
    // Nonuniform Encoding Edwards 25519 SHA512 Elligator2
    //
    //    suite: edwards25519_XMD:SHA-512_ELL2_NU_
    //    dst: QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_
    //
    #[allow(non_upper_case_globals)]
    const edwards25519_XMD_SHA512_ELL2_NU: [xmd_sha512_25519_nu_testcase; 5] = [
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[0],
            P_x: "1ff2b70ecf862799e11b7ae744e3489aa058ce805dd323a936375a84695e76da",
            P_y: "222e314d04a4d5725e9f2aff9fb2a6b69ef375a1214eb19021ceab2d687f0f9b",
            u_0: "7f3e7fb9428103ad7f52db32f9df32505d7b427d894c5093f7a0f0374a30641d",
            Q_x: "42836f691d05211ebc65ef8fcf01e0fb6328ec9c4737c26050471e50803022eb",
            Q_y: "22cb4aaa555e23bd460262d2130d6a3c9207aa8bbb85060928beb263d6d42a95",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[1],
            P_x: "5f13cc69c891d86927eb37bd4afc6672360007c63f68a33ab423a3aa040fd2a8",
            P_y: "67732d50f9a26f73111dd1ed5dba225614e538599db58ba30aaea1f5c827fa42",
            u_0: "09cfa30ad79bd59456594a0f5d3a76f6b71c6787b04de98be5cd201a556e253b",
            Q_x: "333e41b61c6dd43af220c1ac34a3663e1cf537f996bab50ab66e33c4bd8e4e19",
            Q_y: "51b6f178eb08c4a782c820e306b82c6e273ab22e258d972cd0c511787b2a3443",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[2],
            P_x: "1dd2fefce934ecfd7aae6ec998de088d7dd03316aa1847198aecf699ba6613f1",
            P_y: "2f8a6c24dd1adde73909cada6a4a137577b0f179d336685c4a955a0a8e1a86fb",
            u_0: "475ccff99225ef90d78cc9338e9f6a6bb7b17607c0c4428937de75d33edba941",
            Q_x: "55186c242c78e7d0ec5b6c9553f04c6aeef64e69ec2e824472394da32647cfc6",
            Q_y: "5b9ea3c265ee42256a8f724f616307ef38496ef7eba391c08f99f3bea6fa88f0",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[3],
            P_x: "35fbdc5143e8a97afd3096f2b843e07df72e15bfca2eaf6879bf97c5d3362f73",
            P_y: "2af6ff6ef5ebba128b0774f4296cb4c2279a074658b083b8dcca91f57a603450",
            u_0: "049a1c8bd51bcb2aec339f387d1ff51428b88d0763a91bcdf6929814ac95d03d",
            Q_x: "024b6e1621606dca8071aa97b43dce4040ca78284f2a527dcf5d0fbfac2b07e7",
            Q_y: "5102353883d739bdc9f8a3af650342b171217167dcce34f8db57208ec1dfdbf2",
        },
        xmd_sha512_25519_nu_testcase {
            msg: RFC9380_TEST_MESSAGES[4],
            P_x: "6e5e1f37e99345887fc12111575fc1c3e36df4b289b8759d23af14d774b66bff",
            P_y: "2c90c3d39eb18ff291d33441b35f3262cdd307162cc97c31bfcc7a4245891a37",
            u_0: "3cb0178a8137cefa5b79a3a57c858d7eeeaa787b2781be4a362a2f0750d24fa0",
            Q_x: "3e6368cff6e88a58e250c54bd27d2c989ae9b3acb6067f2651ad282ab8c21cd9",
            Q_y: "38fb39f1566ca118ae6c7af42810c0bb9767ae5960abb5a8ca792530bfb9447d",
        },
    ];

    #[allow(non_camel_case_types, non_snake_case)]
    #[derive(Debug)]
    struct xmd_sha512_25519_ro_testcase {
        msg: &'static str,

        // Output
        P_x: &'static str,
        P_y: &'static str,
        u_0: &'static str,
        u_1: &'static str,

        Q0_x: &'static str,
        Q0_y: &'static str,
        Q1_x: &'static str,
        Q1_y: &'static str,
    }

    #[allow(non_camel_case_types, non_snake_case)]
    #[derive(Debug)]
    struct xmd_sha512_25519_nu_testcase {
        msg: &'static str,

        // output
        P_x: &'static str,
        P_y: &'static str,
        u_0: &'static str,

        Q_x: &'static str,
        Q_y: &'static str,
    }


    const RFC9380_TEST_MESSAGES: [&'static str; 5] = [
        "",
        "abc",
        "abcdef0123456789",
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    ];


    trait FromByteString {
        fn must_from_le(&self) -> [u8;32];
        fn must_from_be(&self) -> [u8;32];
    }

    impl<'a> FromByteString for &'a str {
        fn must_from_le(&self) -> [u8;32] {
            let mut u = <[u8;32]>::from_hex(self).unwrap();
            u.reverse();
            u
        }
        fn must_from_be(&self) -> [u8;32] {
            <[u8;32]>::from_hex(self).unwrap()
        }
    }

    trait ToByteString {
        fn encode_le(&self) -> alloc::string::String;
        fn encode_be(&self) -> alloc::string::String;
    }

    impl ToByteString for FieldElement {
        fn encode_le(&self) -> alloc::string::String {
            let mut  b = self.as_bytes();
            b.reverse();
            hex::encode(&b)
        }

        fn encode_be(&self) -> alloc::string::String {
            hex::encode(self.as_bytes())
        }
    }

}
