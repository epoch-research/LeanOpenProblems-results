import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)

lemma symm_P (m : ℕ) (x : ℝ) : (P_witness_gen m).eval x = (P_witness_gen m).eval (1 - x) := by
  unfold P_witness_gen
  simp
  have h1 : 1 - x - 2⁻¹ = -(x - 2⁻¹) := by ring
  rw [h1]
  have h2 (a : ℝ) : a^(2 * m) = (-a)^(2 * m) := by
    rw [neg_eq_neg_one_mul, mul_pow]
    have h_pow : (-1 : ℝ)^(2 * m) = 1 := by
      rw [pow_mul]
      have h_sq : (-1 : ℝ)^2 = 1 := by norm_num
      rw [h_sq, one_pow]
    rw [h_pow, one_mul]
  exact h2 (x - 2⁻¹)
