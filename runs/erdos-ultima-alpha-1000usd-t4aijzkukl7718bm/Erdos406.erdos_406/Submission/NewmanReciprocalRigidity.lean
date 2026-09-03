import Submission.NewmanPowerClassRigidity
import Submission.NewmanReciprocalCandidate

/-! Reciprocal rigidity for normalized binary polynomials. The results do not
bound degrees and do not settle the missing-digit conjecture. -/

namespace Erdos406ReciprocalRigidity
open Polynomial Erdos406ReciprocalFlip Erdos406PowerClass
open Erdos406Cyclotomic Erdos406FactorParity Erdos406ReciprocalCandidate

lemma binary_monic {P : ℤ[X]} (hP : Binary P) (hne : P ≠ 0) : P.Monic := by
  rcases hP P.natDegree with h | h
  · exact ((leadingCoeff_ne_zero.mpr hne) h).elim
  · exact h

lemma normalized_reverse_reverse (Q : ℤ[X]) (hQ : Q.Monic) (h0 : Q.coeff 0 = 1) :
    Q.reverse.reverse = Q := by
  have hd := (monic_reverse_of_constant_one Q hQ h0).2
  change Q.reverse.reflect Q.reverse.natDegree = Q
  rw [hd]
  exact reflect_reflect

/-- A normalized binary polynomial cannot contain a nonreciprocal factor
paired with its reciprocal. No pure-power evaluation is assumed. -/
theorem binary_reciprocal_pair_divisor (P Q : ℤ[X])
    (hP : Binary P) (hP0 : P.coeff 0 = 1) (hQ : Q.Monic) (hQ0 : Q.coeff 0 = 1)
    (hd : Q * Q.reverse ∣ P) : Q.reverse = Q := by
  obtain ⟨R, he⟩ := hd
  have hq0 : Q.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hQ.leadingCoeff]
  have hr0 : R.coeff 0 = 1 := by
    simpa [he, coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q),
      ← coeff_zero_eq_eval_zero (p := Q.reverse), hQ0, hq0] using hP0
  have hb : Binary (Q.reverse ^ 2 * R) := by
    have hh := binary_factor_flip Q (Q.reverse * R) (by simpa [he, mul_assoc] using hP)
    simpa only [pow_two, mul_assoc] using hh
  have h0 : (Q.reverse ^ 2 * R).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q.reverse),
      ← coeff_zero_eq_eval_zero (p := R), hq0, hr0]
  have hh := binary_square_divisor_reciprocal _ Q.reverse hb h0
    (monic_reverse_of_constant_one Q hQ hQ0).1 hq0 (dvd_mul_right _ R)
  rw [normalized_reverse_reverse Q hQ hQ0] at hh
  exact hh.symm

/-- Every monic normalized factor of a reciprocal binary polynomial is
reciprocal, without an irreducibility assumption. -/
theorem binary_reciprocal_factor (P Q : ℤ[X])
    (hP : Binary P) (hP0 : P.coeff 0 = 1) (hrecip : P.reverse = P)
    (hQ : Q.Monic) (hQ0 : Q.coeff 0 = 1) (hd : Q ∣ P) : Q.reverse = Q := by
  obtain ⟨R, he⟩ := hd
  have hPne : P ≠ 0 := by intro hz; simp [hz] at hP0
  have hR : R.Monic := hQ.of_mul_monic_left (by rw [← he]; exact binary_monic hP hPne)
  have hr0 : R.coeff 0 = 1 := by
    simpa [he, coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q), hQ0] using hP0
  have hq0 : Q.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hQ.leadingCoeff]
  have hrr0 : R.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hR.leadingCoeff]
  have hrec : Q * R = Q.reverse * R.reverse := by
    calc
      _ = P := he.symm
      _ = P.reverse := hrecip.symm
      _ = _ := by rw [he, reverse_mul_of_domain]
  have hbS : Binary (Q.reverse * R) := binary_factor_flip Q R (by rwa [← he])
  have hbT : Binary (Q * R.reverse) := by
    have hh := binary_factor_flip R Q (by simpa [mul_comm, ← he] using hP)
    simpa [mul_comm] using hh
  have ht0 : (Q * R.reverse).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q),
      ← coeff_zero_eq_eval_zero (p := R.reverse), hQ0, hrr0]
  have hsame : Q.reverse * R = Q * R.reverse := by
    apply binary_power_ratio_unique (Q.reverse * R) (Q * R.reverse) Q Q.reverse 2
      hbS hbT ht0 hQ0 hq0 (by decide)
    calc
      _ = (Q * Q.reverse) * (Q * R) := by ring
      _ = (Q * Q.reverse) * (Q.reverse * R.reverse) := by rw [hrec]
      _ = _ := by ring
  have hsq : Q ^ 2 = Q.reverse ^ 2 := by
    apply mul_right_cancel₀ (show R.reverse ≠ 0 by simpa using hR.ne_zero)
    calc
      Q ^ 2 * R.reverse = Q * (Q * R.reverse) := by ring
      _ = Q * (Q.reverse * R) := by rw [hsame]
      _ = Q.reverse * (Q * R) := by ring
      _ = Q.reverse * (Q.reverse * R.reverse) := by rw [hrec]
      _ = _ := by ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
  · exact hh.symm
  · have hc := congrArg (fun f : ℤ[X] => f.coeff 0) hh
    simp [hQ0, hq0] at hc

theorem reciprocal_digit_factor (w : List ℕ) (hw : w ⊆ [0, 1])
    (hrecip : (digitPoly (1 :: w)).reverse = digitPoly (1 :: w))
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ digitPoly (1 :: w)) : Q.reverse = Q := by
  exact binary_reciprocal_factor _ Q (binary_digitPoly _ (by simpa using hw))
    (by simp [digitPoly, Nat.ofDigits]) hrecip hQ
    (monic_factor_constant_one w Q hQ hd) hd

#print axioms binary_reciprocal_pair_divisor
#print axioms binary_reciprocal_factor
#print axioms reciprocal_digit_factor

/-- Reciprocal ternary digits and an even square value do not force a power
of two. The odd prime divisor 131 prevents this example from being a
counterexample to the original conjecture. -/
theorem even_palindromic_square_example :
    Even (262 : ℕ) ∧ 262 ^ 2 = 68644 ∧
      Nat.digits 3 (262 ^ 2) ⊆ [0, 1] ∧
      (Nat.digits 3 (262 ^ 2)).reverse = Nat.digits 3 (262 ^ 2) ∧
      ¬ (262 ^ 2).isPowerOfTwo := by
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨k, hk⟩
  have hd : 131 ∣ 2 ^ k := by rw [← hk]; decide
  have hp : Nat.Prime 131 := by norm_num
  have hh := hp.dvd_of_dvd_pow hd
  norm_num at hh

#print axioms even_palindromic_square_example


end Erdos406ReciprocalRigidity
