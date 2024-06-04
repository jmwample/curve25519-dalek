// -*- mode: rust; -*-

//! Functions mapping curve points to representative values
//! (indistinguishable from random), and back again.
use crate::backend::serial::u64::constants::SQRT_M1;
use crate::constants::{MONTGOMERY_A, MONTGOMERY_A_NEG};
use crate::field::FieldElement;
use crate::montgomery::MontgomeryPoint;
use crate::EdwardsPoint;

use subtle::{
    Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
    CtOption,
};

/// bitmask for a single byte when clearing the high order two bits of a representative
pub(crate) const MASK_UNSET_BYTE: u8 = 0x3f;
/// bitmask for a single byte when setting the high order two bits of a representative
pub(crate) const MASK_SET_BYTE: u8 = 0xc0;

/// (p - 1) / 2 = 2^254 - 10
pub(crate) const DIVIDE_MINUS_P_1_2_BYTES: [u8; 32] = [
    0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
];

/// Gets a public representative for a key pair using the private key.
///
/// The `tweak` parameter is used to adjust the computed representative making
/// it computationally indistinguishable from uniform random. If this property
/// is not required then the provided tweak value does not matter.
///
/// The tweak allows us to overcome three limitations:
/// - Representatives are not always canonical.
/// - Bit 255 (the most significant bit) was always zero.
/// - Only points from the large prime-order subgroup are represented.
///
/// In order for the returned representative to be canonical a tweak to the
/// high order two bits must be applied.
/// ```txt
/// [An adversary could] observe a representative, interpret it as a field
/// element, square it, then take the square root using the same
/// non-canonical square root algorithm. With representatives produced by
/// an affected version of [the elligator2 implementation], the output of
/// the square-then-root operation would always match the input. With
/// random strings, the output would match only half the time.
/// ```
///
/// For a more in-depth explanation see:
/// https://github.com/agl/ed25519/issues/27
/// https://www.bamsoftware.com/papers/fep-flaws/
pub fn representative_from_privkey(privkey: &[u8; 32], tweak: u8) -> Option<[u8; 32]> {
    /*
    let pubkey = EdwardsPoint::mul_base_clamped(*privkey).to_montgomery();
    let v_in_sqrt = v_in_sqrt(privkey);
    let p: Option<[u8; 32]> = point_to_representative(&pubkey, v_in_sqrt.into()).into();
    match p {
        None => None,
        Some(mut a) => {
            a[31] |= MASK_SET_BYTE & tweak;
            Some(a)
        }
    }
    */

    let u = EdwardsPoint::mul_base_clamped_dirty(*privkey);
    representative_from_pubkey(&u, tweak).into()
}

/// Low order point Edwards x-coordinate `sqrt((sqrt(d + 1) + 1) / d)`.
const LOW_ORDER_POINT_X: FieldElement = FieldElement::from_limbs([
    0x00014646c545d14a,
    0x0006027cbc471bd4,
    0x0003792aed7064f1,
    0x0005147499cc991c,
    0x0001fd5b9a006394,
]);
/// Low order point Edwards y-coordinate `-lop_x * sqrtm1`
const LOW_ORDER_POINT_Y: FieldElement = FieldElement::from_limbs([
    0x0007b2c28f95e826,
    0x0006513e9868b604,
    0x0006b37f57c263bf,
    0x0004589c99e36982,
    0x00005fc536d88023,
]);

const FE_MINUS_TWO: FieldElement = FieldElement::from_limbs([
    2251799813685227,
    2251799813685247,
    2251799813685247,
    2251799813685247,
    2251799813685247,
]);

fn select_low_order_point(a: &FieldElement, b: &FieldElement, cofactor: u8) -> FieldElement {
    // bit 0
    let c0 = !Choice::from((cofactor >> 1) & 1);
    let out = FieldElement::conditional_select(b, &FieldElement::ZERO, c0);

    // bit 1
    let c1 = !Choice::from((cofactor >> 0) & 1);
    let mut out = FieldElement::conditional_select(a, &out, c1);

    // bit 2
    let c2 = Choice::from((cofactor >> 2) & 1);
    out.conditional_negate(c2);
    out
}

#[cfg(feature = "alloc")]
impl EdwardsPoint {
    /// Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub(crate) fn mul_base_clamped_dirty(privkey: [u8; 32]) -> Self {
        let lop_x = select_low_order_point(&LOW_ORDER_POINT_X, &SQRT_M1, privkey[0]);
        let (cofactor, _) = privkey[0].overflowing_add(2);
        let lop_y = select_low_order_point(&LOW_ORDER_POINT_Y, &FieldElement::ONE, cofactor);
        let lop_t = &lop_x * &lop_y;

        let low_order_point = EdwardsPoint {
            X: lop_x,
            Y: lop_y,
            Z: FieldElement::ONE,
            T: lop_t,
        };

        // add the low order point to the public key
        EdwardsPoint::mul_base_clamped(privkey) + &low_order_point
    }
}

/// Gets the pulic representative using the ['EdwardsPoint'] public key.
fn representative_from_pubkey(pubkey: &EdwardsPoint, tweak: u8) -> CtOption<[u8; 32]> {
    let mut t1 = FieldElement::from_bytes(&pubkey.to_montgomery().0);

    // -2 * u * (u + A)
    let t2 = &t1 + &MONTGOMERY_A;
    let t3 = &(&t1 * &t2) * &FE_MINUS_TWO;

    let (is_sq, mut t3) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, &t3);

    t1 = FieldElement::conditional_select(&t1, &t2, Choice::from(tweak & 1));
    t3 = &t1 * &t3;
    t1 = &t3 + &t3;

    let tmp: u8 = t1.as_bytes()[0] & 1;
    t3.conditional_negate(Choice::from(tmp));

    // get representative and pad with bits from the tweak.
    let mut representative = t3.as_bytes();
    representative[31] |= tweak & MASK_SET_BYTE;

    CtOption::new(representative, is_sq)
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
    let mut a_neg = *a;
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
    let au = &MONTGOMERY_A * d;

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
    let mut masked_pk = *key_input;
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
    divide_minus_p_1_2.ct_gt(&v)
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

fn map_to_curve_parts(
    r: &FieldElement,
) -> (FieldElement, FieldElement, FieldElement, FieldElement) {
    let zero = FieldElement::ZERO;
    let one = FieldElement::ONE;
    let mut minus_one = FieldElement::ONE;
    minus_one.negate();

    // Exceptional case 2u^2 == -1
    let mut tv1 = r.square2();
    tv1.conditional_assign(&zero, tv1.ct_eq(&minus_one));

    let d_1 = &one + &tv1; /* 1 + 2u^2 */
    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* d = -A/(1+2u^2) */

    let inner = &(&d.square() + &(&d * &MONTGOMERY_A)) + &one;
    let gx1 = &d * &inner; /* gx1 = d^3 + Ad^2 + d */
    let gx2 = &gx1 * &tv1;

    let eps_is_sq = high_y(&d);

    // complete X
    /* A_temp = 0, or A if nonsquare*/
    let a_temp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq);
    let mut x = &d + &a_temp; /* d, or d+A if nonsquare */
    x.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    // complete Y
    let y2 = FieldElement::conditional_select(&gx2, &gx1, eps_is_sq);
    let (_, mut y) = FieldElement::sqrt_ratio_i(&y2, &one);
    y.conditional_negate(eps_is_sq ^ y.is_negative());

    (&x * &d_1, d_1, y, one)
}

pub(crate) fn map_fe_to_montgomery(r: &FieldElement) -> (FieldElement, FieldElement) {
    let (xmn, xmd, y, _) = map_to_curve_parts(r);
    (&xmn * &(xmd.invert()), y)
}

pub(crate) fn map_fe_to_edwards(r: &FieldElement) -> (FieldElement, FieldElement) {
    // 1.  (xMn, xMd, yMn, yMd) = map_to_curve_elligator2_curve25519(u)
    let (xmn, xmd, ymn, ymd) = map_to_curve_parts(r);
    // c1 = sqrt(-486664)
    // this cannot fail as it computes a constant
    let c1 = &(&MONTGOMERY_A_NEG - &FieldElement::ONE) - &FieldElement::ONE;
    let (_, c1) = FieldElement::sqrt_ratio_i(&c1, &FieldElement::ONE);

    // 2.  xn = xMn * yMd
    // 3.  xn = xn * c1
    let mut xn = &(&xmn * &ymd) * &c1;

    // 4.  xd = xMd * yMn    # xn / xd = c1 * xM / yM
    let mut xd = &xmd * &ymn;

    // 5.  yn = xMn - xMd
    let mut yn = &xmn - &xmd;
    // 6.  yd = xMn + xMd    # (n / d - 1) / (n / d + 1) = (n - d) / (n + d)
    let mut yd = &xmn + &xmd;

    // 7. tv1 = xd * yd
    // 8.   e = tv1 == 0
    let cond = (&xd * &yd).is_zero();

    // 9.  xn = CMOV(xn, 0, e)
    // 10. xd = CMOV(xd, 1, e)
    // 11. yn = CMOV(yn, 1, e)
    // 12. yd = CMOV(yd, 1, e)
    xn = FieldElement::conditional_select(&xn, &FieldElement::ZERO, cond);
    xd = FieldElement::conditional_select(&xd, &FieldElement::ONE, cond);
    yn = FieldElement::conditional_select(&yn, &FieldElement::ONE, cond);
    yd = FieldElement::conditional_select(&yd, &FieldElement::ONE, cond);

    // 13. return (xn, xd, yn, yd)
    (&xn * &(xd.invert()), &yn * &(yd.invert()))
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
#[cfg(feature = "elligator2")]
#[cfg(feature = "alloc")]
mod compatibility;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod rfc9380;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod randomness;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod subgroup;
