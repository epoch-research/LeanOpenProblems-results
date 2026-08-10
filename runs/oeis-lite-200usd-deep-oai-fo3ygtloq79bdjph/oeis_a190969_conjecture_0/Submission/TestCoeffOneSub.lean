import FormalConjectures.Util.ProblemImports
open Polynomial
lemma hpoly : (1 - (X : ℤ[X])) = - (X + C (-1 : ℤ)) := by
  ext k
  by_cases h0 : k = 0
  · subst k; simp
  · by_cases h1 : k = 1
    · subst k; simp; ring
    · simp [coeff_sub, Polynomial.coeff_X]; ring
lemma test (n m : ℕ) :
    ((1 - (X : ℤ[X])) ^ n).coeff m = (-1 : ℤ)^m * (n.choose m : ℤ) := by
  rw [hpoly, neg_pow]
  rw [show ((-1 : ℤ[X]) ^ n) = C ((-1 : ℤ)^n) by simp]
  rw [coeff_C_mul, coeff_X_add_C_pow]
  by_cases hm : m ≤ n
  · have h : n + (n - m) = m + 2 * (n - m) := by omega
    rw [← mul_assoc, ← pow_add, h, pow_add]
    norm_num
  · have hlt : n < m := Nat.lt_of_not_ge hm
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
