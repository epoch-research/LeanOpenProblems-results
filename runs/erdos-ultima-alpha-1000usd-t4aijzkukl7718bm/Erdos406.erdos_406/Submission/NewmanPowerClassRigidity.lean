import Submission.NewmanReciprocalFlip
import Submission.CyclotomicObstruction

/-! Binary polynomials are rigid under normalized perfect-power ratios.
This concerns polynomial identities, not identities after evaluation at three.
The known good power 256 explicitly separates the two conditions. -/

namespace Erdos406PowerClass
open Polynomial Erdos406ReciprocalFlip Erdos406Cyclotomic

/-- Two binary polynomials cannot differ by a nontrivial perfect-power ratio
whose numerator and denominator have constant coefficient one. -/
theorem binary_power_ratio_unique (P A B C : ℤ[X]) (r : ℕ)
    (hP : Binary P) (hA : Binary A) (hA0 : A.coeff 0 = 1)
    (hB0 : B.coeff 0 = 1) (hC0 : C.coeff 0 = 1) (hr : 2 ≤ r)
    (he : P * B ^ r = A * C ^ r) : P = A := by
  by_contra hne
  let S : ℤ[X] := ∑ i ∈ Finset.range r, C ^ i * B ^ (r - 1 - i)
  have hS : S * (C - B) = C ^ r - B ^ r := geom_sum₂_mul C B r
  have hAe : A.eval 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hA0
  have hBe : B.eval 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hB0
  have hCe : C.eval 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hC0
  have hS0 : S.coeff 0 = (r : ℤ) := by
    simp [S, coeff_zero_eq_eval_zero, eval_finset_sum, hBe, hCe]
  have hTA : A.trailingCoeff = 1 := by
    rw [trailingCoeff_eq_coeff_zero (by omega : A.coeff 0 ≠ 0), hA0]
  have hTB : (B ^ r).trailingCoeff = 1 := by
    have hh : (B ^ r).coeff 0 = 1 := by simp [coeff_zero_eq_eval_zero, hBe]
    rw [trailingCoeff_eq_coeff_zero (by omega : (B ^ r).coeff 0 ≠ 0), hh]
  have hTS : S.trailingCoeff = (r : ℤ) := by
    rw [trailingCoeff_eq_coeff_zero (by rw [hS0]; omega), hS0]
  have hid : (P - A) * B ^ r = A * S * (C - B) := by
    calc
      _ = P * B ^ r - A * B ^ r := by ring
      _ = A * (C ^ r - B ^ r) := by rw [he]; ring
      _ = _ := by rw [← hS]; ring
  have ht := congrArg trailingCoeff hid
  simp only [trailingCoeff_mul, hTA, hTB, hTS, mul_one, one_mul] at ht
  have hd : (r : ℤ) ∣ (P - A).trailingCoeff := ⟨(C - B).trailingCoeff, ht⟩
  have hn : (P - A).trailingCoeff ≠ 0 := by
    simpa only [ne_eq, trailingCoeff_eq_zero, sub_eq_zero] using hne
  have hb : (P - A).trailingCoeff.natAbs ≤ 1 := by
    unfold trailingCoeff
    rw [coeff_sub]
    rcases hP (P - A).natTrailingDegree with hp | hp <;>
      rcases hA (P - A).natTrailingDegree with ha | ha <;> simp [hp, ha]
  have hh := Int.natAbs_le_of_dvd_ne_zero hd hn
  rw [Int.natAbs_natCast] at hh
  omega

/-- In particular, multiplying a binary polynomial by a normalized square
cannot produce a different binary polynomial. -/
theorem binary_square_multiple_unique (P A Q : ℤ[X])
    (hP : Binary P) (hA : Binary A) (hA0 : A.coeff 0 = 1)
    (hQ0 : Q.coeff 0 = 1) (he : P = A * Q ^ 2) : P = A := by
  apply binary_power_ratio_unique P A 1 Q 2 hP hA hA0 (by simp) hQ0 (by decide)
  simpa using he

lemma binary_one : Binary (1 : ℤ[X]) := by
  intro i
  by_cases hi : i = 0 <;> simp [coeff_one, hi]

lemma binary_X_add_one : Binary (X + 1 : ℤ[X]) := by
  intro i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [coeff_add, coeff_X, coeff_one, eq_comm, *]

/-- A normalized binary polynomial that is an integer polynomial square is one. -/
theorem binary_square_eq_one (P Q : ℤ[X]) (hP : Binary P)
    (hP0 : P.coeff 0 = 1) (he : P = Q ^ 2) : P = 1 := by
  have hq : Q.coeff 0 = 1 ∨ Q.coeff 0 = -1 := by
    have hh : (Q.coeff 0) ^ 2 = 1 := by
      simpa only [he, coeff_zero_eq_eval_zero, eval_pow] using hP0
    have hz : (Q.coeff 0 - 1) * (Q.coeff 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h <;> omega
  rcases hq with hq | hq
  · exact binary_square_multiple_unique P 1 Q hP binary_one (by simp) hq (by simpa using he)
  · exact binary_square_multiple_unique P 1 (-Q) hP binary_one (by simp)
      (by simp [hq]) (by simpa using he)

/-- The same rigidity holds when the squarefree kernel is X+1. -/
theorem binary_X_add_one_times_square (P Q : ℤ[X]) (hP : Binary P)
    (hP0 : P.coeff 0 = 1) (he : P = (X + 1) * Q ^ 2) : P = X + 1 := by
  have hq : Q.coeff 0 = 1 ∨ Q.coeff 0 = -1 := by
    have hh : (Q.coeff 0) ^ 2 = 1 := by
      simpa [he, coeff_zero_eq_eval_zero] using hP0
    have hz : (Q.coeff 0 - 1) * (Q.coeff 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h <;> omega
  rcases hq with hq | hq
  · exact binary_square_multiple_unique P (X + 1) Q hP binary_X_add_one (by simp) hq he
  · exact binary_square_multiple_unique P (X + 1) (-Q) hP binary_X_add_one (by simp)
      (by simp [hq]) (by simpa using he)

#print axioms binary_power_ratio_unique
#print axioms binary_square_eq_one
#print axioms binary_X_add_one_times_square


/-- Every normalized monic square divisor of a binary polynomial is reciprocal.
This does not say that all factors are reciprocal: simple nonreciprocal factors
are not excluded. -/
theorem binary_square_divisor_reciprocal (P Q : ℤ[X])
    (hP : Binary P) (hP0 : P.coeff 0 = 1)
    (hQ : Q.Monic) (hQ0 : Q.coeff 0 = 1) (hd : Q ^ 2 ∣ P) :
    Q.reverse = Q := by
  obtain ⟨R, he⟩ := hd
  have hr0 : R.coeff 0 = 1 := by
    simpa [he, coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q), hQ0] using hP0
  have hrne : R ≠ 0 := by intro hz; simp [hz] at hr0
  have hqrev0 : Q.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hQ.leadingCoeff]
  have hflip : Binary (Q.reverse ^ 2 * R) := by
    have hh := binary_factor_flip (Q ^ 2) R (by simpa [← he] using hP)
    simpa only [pow_two, reverse_mul_of_domain] using hh
  have hflip0 : (Q.reverse ^ 2 * R).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero (p := Q.reverse),
      ← coeff_zero_eq_eval_zero (p := R), hqrev0, hr0]
  have hsame : P = Q.reverse ^ 2 * R := by
    apply binary_power_ratio_unique P (Q.reverse ^ 2 * R) Q.reverse Q 2
      hP hflip hflip0 hqrev0 hQ0 (by decide)
    rw [he]
    ring
  have hsq : Q ^ 2 = Q.reverse ^ 2 := by
    apply mul_right_cancel₀ hrne
    exact he.symm.trans hsame
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h.symm
  · have hc := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simp [hQ0, hqrev0] at hc

/-- Thus a nonreciprocal normalized monic divisor can occur only once. -/
theorem nonreciprocal_multiplicity_le_one (P Q : ℤ[X]) (m : ℕ)
    (hP : Binary P) (hP0 : P.coeff 0 = 1)
    (hQ : Q.Monic) (hQ0 : Q.coeff 0 = 1) (hneq : Q.reverse ≠ Q)
    (hd : Q ^ m ∣ P) : m ≤ 1 := by
  by_contra hm
  exact hneq (binary_square_divisor_reciprocal P Q hP hP0 hQ hQ0
    ((pow_dvd_pow Q (by omega : 2 ≤ m)).trans hd))

#print axioms binary_square_divisor_reciprocal
#print axioms nonreciprocal_multiplicity_le_one

end Erdos406PowerClass
