// -*- mode: rust; coding: utf-8; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Field arithmetic modulo \\(p = 2\^{255} - 19\\), using \\(64\\)-bit
//! limbs with \\(128\\)-bit products.
//!
//! This uses the formally-verified field arithmetic generated by the
//! [fiat-crypto project](https://github.com/mit-plv/fiat-crypto)

use core::fmt::Debug;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};

use subtle::Choice;
use subtle::ConditionallySelectable;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use fiat_crypto::curve25519_64::*;

/// A `FieldElement51` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 64-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{51}\\) as five `u64`s; the coefficients are allowed to
/// grow up to \\(2\^{54}\\) between reductions modulo \\(p\\).
///
/// # Note
///
/// The `curve25519_dalek::field` module provides a type alias
/// `curve25519_dalek::field::FieldElement` to either `FieldElement51`
/// or `FieldElement2625`.
///
/// The backend-specific type `FieldElement51` should not be used
/// outside of the `curve25519_dalek::field` module.
#[derive(Copy, Clone)]
pub struct FieldElement51(pub(crate) fiat_25519_tight_field_element);

impl Debug for FieldElement51 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FieldElement51({:?})", &(self.0).0[..])
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for FieldElement51 {
    fn zeroize(&mut self) {
        (self.0).0.zeroize();
    }
}

impl<'b> AddAssign<&'b FieldElement51> for FieldElement51 {
    fn add_assign(&mut self, rhs: &'b FieldElement51) {
        let mut result_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_add(&mut result_loose, &self.0, &rhs.0);
        fiat_25519_carry(&mut self.0, &result_loose);
    }
}

impl<'a, 'b> Add<&'b FieldElement51> for &'a FieldElement51 {
    type Output = FieldElement51;
    fn add(self, rhs: &'b FieldElement51) -> FieldElement51 {
        let mut result_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_add(&mut result_loose, &self.0, &rhs.0);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry(&mut output.0, &result_loose);
        output
    }
}

impl<'b> SubAssign<&'b FieldElement51> for FieldElement51 {
    fn sub_assign(&mut self, rhs: &'b FieldElement51) {
        let mut result_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_sub(&mut result_loose, &self.0, &rhs.0);
        fiat_25519_carry(&mut self.0, &result_loose);
    }
}

impl<'a, 'b> Sub<&'b FieldElement51> for &'a FieldElement51 {
    type Output = FieldElement51;
    fn sub(self, rhs: &'b FieldElement51) -> FieldElement51 {
        let mut result_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_sub(&mut result_loose, &self.0, &rhs.0);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry(&mut output.0, &result_loose);
        output
    }
}

impl<'b> MulAssign<&'b FieldElement51> for FieldElement51 {
    fn mul_assign(&mut self, rhs: &'b FieldElement51) {
        let mut self_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut self_loose, &self.0);
        let mut rhs_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut rhs_loose, &rhs.0);
        fiat_25519_carry_mul(&mut self.0, &self_loose, &rhs_loose);
    }
}

impl<'a, 'b> Mul<&'b FieldElement51> for &'a FieldElement51 {
    type Output = FieldElement51;
    fn mul(self, rhs: &'b FieldElement51) -> FieldElement51 {
        let mut self_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut self_loose, &self.0);
        let mut rhs_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut rhs_loose, &rhs.0);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry_mul(&mut output.0, &self_loose, &rhs_loose);
        output
    }
}

impl<'a> Neg for &'a FieldElement51 {
    type Output = FieldElement51;
    fn neg(self) -> FieldElement51 {
        let mut output_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_opp(&mut output_loose, &self.0);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry(&mut output.0, &output_loose);
        output
    }
}

impl ConditionallySelectable for FieldElement51 {
    fn conditional_select(
        a: &FieldElement51,
        b: &FieldElement51,
        choice: Choice,
    ) -> FieldElement51 {
        let mut output = fiat_25519_tight_field_element([0u64; 5]);
        fiat_25519_selectznz(
            &mut output.0,
            choice.unwrap_u8() as fiat_25519_u1,
            &(a.0).0,
            &(b.0).0,
        );
        FieldElement51(output)
    }

    fn conditional_swap(a: &mut FieldElement51, b: &mut FieldElement51, choice: Choice) {
        u64::conditional_swap(&mut a.0[0], &mut b.0[0], choice);
        u64::conditional_swap(&mut a.0[1], &mut b.0[1], choice);
        u64::conditional_swap(&mut a.0[2], &mut b.0[2], choice);
        u64::conditional_swap(&mut a.0[3], &mut b.0[3], choice);
        u64::conditional_swap(&mut a.0[4], &mut b.0[4], choice);
    }

    fn conditional_assign(&mut self, rhs: &FieldElement51, choice: Choice) {
        let mut output = [0u64; 5];
        let choicebit = choice.unwrap_u8() as fiat_25519_u1;
        fiat_25519_cmovznz_u64(&mut output[0], choicebit, self.0[0], rhs.0[0]);
        fiat_25519_cmovznz_u64(&mut output[1], choicebit, self.0[1], rhs.0[1]);
        fiat_25519_cmovznz_u64(&mut output[2], choicebit, self.0[2], rhs.0[2]);
        fiat_25519_cmovznz_u64(&mut output[3], choicebit, self.0[3], rhs.0[3]);
        fiat_25519_cmovznz_u64(&mut output[4], choicebit, self.0[4], rhs.0[4]);
        *self = FieldElement51::from_limbs(output);
    }
}

impl FieldElement51 {
    pub(crate) const fn from_limbs(limbs: [u64; 5]) -> FieldElement51 {
        FieldElement51(fiat_25519_tight_field_element(limbs))
    }

    /// The scalar \\( 0 \\).
    pub const ZERO: FieldElement51 = FieldElement51::from_limbs([0, 0, 0, 0, 0]);
    /// The scalar \\( 1 \\).
    pub const ONE: FieldElement51 = FieldElement51::from_limbs([1, 0, 0, 0, 0]);
    /// The scalar \\( -1 \\).
    pub const MINUS_ONE: FieldElement51 = FieldElement51::from_limbs([
        2251799813685228,
        2251799813685247,
        2251799813685247,
        2251799813685247,
        2251799813685247,
    ]);

    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    #[inline(always)]
    #[allow(dead_code)] // Need this to not complain about reduce not being used
    fn reduce(limbs: [u64; 5]) -> FieldElement51 {
        let input = fiat_25519_loose_field_element(limbs);
        let mut output = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_carry(&mut output, &input);
        FieldElement51(output)
    }

    /// Load a `FieldElement51` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    ///
    pub fn from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
        let mut temp = [0u8; 32];
        temp.copy_from_slice(bytes);
        temp[31] &= 127u8;
        let mut output = fiat_25519_tight_field_element([0u64; 5]);
        fiat_25519_from_bytes(&mut output, &temp);
        FieldElement51(output)
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    pub fn as_bytes(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        fiat_25519_to_bytes(&mut bytes, &self.0);
        bytes
    }

    /// Given `k > 0`, return `self^(2^k)`.
    pub fn pow2k(&self, mut k: u32) -> FieldElement51 {
        let mut output = *self;
        loop {
            let mut input = fiat_25519_loose_field_element([0; 5]);
            fiat_25519_relax(&mut input, &output.0);
            fiat_25519_carry_square(&mut output.0, &input);
            k -= 1;
            if k == 0 {
                return output;
            }
        }
    }

    /// Returns the square of this field element.
    pub fn square(&self) -> FieldElement51 {
        let mut self_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut self_loose, &self.0);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry_square(&mut output.0, &self_loose);
        output
    }

    /// Returns 2 times the square of this field element.
    pub fn square2(&self) -> FieldElement51 {
        let mut self_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_relax(&mut self_loose, &self.0);
        let mut square = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_carry_square(&mut square, &self_loose);
        let mut output_loose = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_add(&mut output_loose, &square, &square);
        let mut output = FieldElement51::ZERO;
        fiat_25519_carry(&mut output.0, &output_loose);
        output
    }

    /// Returns 1 if self is greater than the other and 0 otherwise
    // implementation based on C libgmp -> mpn_sub_n
    pub(crate) fn gt(&self, other: &Self) -> Choice {
        let mut _ul = 0_u64;
        let mut _vl = 0_u64;
        let mut _rl = 0_u64;

        let mut cy = 0_u64;
        for i in 0..5 {
            _ul = self.0[i];
            _vl = other.0[i];

            let (_sl, _cy1) = _ul.overflowing_sub(_vl);
            let (_rl, _cy2) = _sl.overflowing_sub(cy);
            cy = _cy1 as u64 | _cy2 as u64;
        }

        Choice::from((cy != 0_u64) as u8)
    }
}
