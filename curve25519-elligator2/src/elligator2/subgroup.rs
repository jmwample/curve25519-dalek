use super::*;
use crate::{MontgomeryPoint, traits::IsIdentity};
use crate::scalar::test::BASEPOINT_ORDER_MINUS_ONE;

use rand::Rng;
use rand_core::{CryptoRng, RngCore};


// Generates a new Keypair using, and returns the public key representative
// along, with its public key as a newly allocated edwards25519.Point.
fn generate<R:RngCore+CryptoRng>(rng: &mut R) -> ([u8; 32], EdwardsPoint) {
    for _ in 0..63 {
        let y_sk = rng.gen::<[u8; 32]>();
        let y_sk_tweak = rng.next_u32() as u8;

        let y_repr_bytes = match Randomized::to_representative(&y_sk, y_sk_tweak).into() {
            Some(r) => r,
            None => continue,
        };
        let y_pk = Randomized::mul_base_clamped(y_sk);

        assert_eq!(
            MontgomeryPoint::from_representative::<Randomized>(&y_repr_bytes)
                .expect("failed to re-derive point from representative"),
            y_pk.to_montgomery()
        );

        return (y_repr_bytes, y_pk);
    }
    panic!("failed to generate a valid keypair");
}

/// Returns a new edwards25519.Point that is v multiplied by the subgroup order.
///
/// BASEPOINT_ORDER_MINUS_ONE is the same as scMinusOne in filippo.io/edwards25519.
/// https://github.com/FiloSottile/edwards25519/blob/v1.0.0/scalar.go#L34
fn scalar_mult_order(v: &EdwardsPoint) -> EdwardsPoint {
        // v * (L - 1) + v => v * L
        let p = v * BASEPOINT_ORDER_MINUS_ONE;
        p + v
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
fn pubkey_subgroup_check() {
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

    let mut rng = rand::thread_rng();
    for _ in 0..255 {
        let (repr, pk) = generate(&mut rng);
        let v = scalar_mult_order(&pk);

        let b = v.compress().to_bytes();
        let b_str = hex::encode(b);
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
    for count in counts.iter() {
        if *count == 0 {
            failed = true;
        }
    }

    if failed {
        panic!("not all low order points were covered")
    }
}

#[test]
fn off_subgroup_check_edw() {
    let mut rng = rand::thread_rng();
    for _ in 0..100 {
        let (repr, pk) = generate(&mut rng);

        // check if the generated public key is off the subgroup
        let v = scalar_mult_order(&pk);
        let pk_off = !v.is_identity();

        // --- 

        // check if the public key derived from the representative (top bit 0)
        // is off the subgroup
        let mut yr_255 = repr.clone();
        yr_255[31] &= 0xbf;
        let pk_255 = EdwardsPoint::from_representative::<RFC9380>(&yr_255).expect("from_repr_255, should never fail");
        let v = scalar_mult_order(&pk_255);
        let off_255 = !v.is_identity();

        // check if the public key derived from the representative (top two bits 0 - as
        // our representatives are) is off the subgroup.
        let mut yr_254 = repr.clone();
        yr_254[31] &= 0x3f;
        let pk_254 = EdwardsPoint::from_representative::<RFC9380>(&yr_254).expect("from_repr_254, should never fail");
        let v = scalar_mult_order(&pk_254);
        let off_254 = !v.is_identity();

        println!("pk_gen: {pk_off}, pk_255: {off_255}, pk_254: {off_254}");
    }
}

use crate::constants::BASEPOINT_ORDER_PRIVATE;

fn check(pk: MontgomeryPoint) -> bool {
    let z = pk * BASEPOINT_ORDER_PRIVATE;
    !z.is_identity()
}

/// check a point in the group, assuming it is a representative and given a
/// variant by which to convert it to a point.
fn check_r<V:MapToPointVariant>(r: [u8;32]) -> bool {
    let pk = MontgomeryPoint::from_representative::<V>(&r).expect("from_representative failed");
    check(pk)
}

#[test]
/// Somehow there should be a montgomery distinguisher where all real representatives
/// map to the curve subgroup. For our keys this should only (consistently) happen
/// for representatives with the top two bits cleared (i.e. 254 but representatives).
fn off_subgroup_check_mgt() {
    let mut rng = rand::thread_rng();

    for _ in 0..100 {
        let (mut repr, pk) = generate(&mut rng);
        repr[31] &= MASK_UNSET_BYTE;

        let off_pk = check(pk.to_montgomery());

        let off_rfc = check_r::<RFC9380>(repr);

        let off_rand = check_r::<Randomized>(repr);

        let (u, _v) = elligator_dir_map(repr);
        let u = MontgomeryPoint(u.as_bytes());
        let off = check(u);

        println!("pk: {off_pk},\trfc: {off_rfc},\trand: {off_rand},\tcust: {off}");
    }
}

#[test]
/// Somehow there should be a montgomery distinguisher where all real representatives
/// map to the curve subgroup. For our keys this should only (consistently) happen
/// for representatives with the top two bits cleared (i.e. 254 but representatives).
fn off_subgroup_check_custom() {
    let mut rng = rand::thread_rng();

    for _ in 0..100 {
        let (mut repr, _) = generate(&mut rng);
        repr[31] &= MASK_UNSET_BYTE;

        let (u, _v) = elligator_dir_map(repr);
        let u = MontgomeryPoint(u.as_bytes());
        let off = check(u);

        println!("custom: {off}");
    }
}


/// Direct elligator map translate as accurately as possible from `obfs4-subgroup-check.py`.
fn elligator_dir_map(rb: [u8;32]) -> (FieldElement, FieldElement) {
    let r = FieldElement::from_bytes(&rb);
    let two = &FieldElement::ONE + &FieldElement::ONE;
    let ufactor = &-&two * &SQRT_M1; 
    let (_, vfactor) = FieldElement::sqrt_ratio_i(&ufactor, &FieldElement::ONE);


    let u = r.square();
    let t1 = r.square2();
    let v = &t1 + &FieldElement::ONE;
    let t2 = v.square();
    let t3 = MONTGOMERY_A.square();
    let t3 = &t3 * &t1;
    let t3 = &t3 - &t2;
    let t3 = &t3 * &MONTGOMERY_A;
    let t1 = &t2 * &v;

    let (is_sq, t1) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, &(&t3 * &t1));
    let u = &u * &ufactor;
    let v = &r * &vfactor;
    let u = FieldElement::conditional_select(&u, &FieldElement::ONE, is_sq);
    let v = FieldElement::conditional_select(&v, &FieldElement::ONE, is_sq);
    let v = &v * &t3;
    let v = &v * &t1;
    let t1 = t1.square();
    let u = &u * &-&MONTGOMERY_A;
    let u = &u * &t3;
    let u = &u * &t2;
    let u = &u * &t1;
    let t1  = -&v;
    let v =  FieldElement::conditional_select(&v, &t1, is_sq ^ v.is_negative());
    (u, v)
}
