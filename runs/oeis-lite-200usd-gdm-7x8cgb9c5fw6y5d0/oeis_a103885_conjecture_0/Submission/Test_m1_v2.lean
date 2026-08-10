import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P : Polynomial ℝ := 5 * X^2 - 5 * X + 1

lemma coeff_P_above (N : ℕ) (hN : 2 < N) : P.coeff N = 0 := by
  unfold P
  simp [coeff_add, coeff_sub, coeff_X_pow, hN]
  have hN1 : N ≠ 2 := by omega
  have hN2 : N ≠ 1 := by omega
  have hN3 : N ≠ 0 := by omega
  -- Wait, let's see what simp does
  sorry
