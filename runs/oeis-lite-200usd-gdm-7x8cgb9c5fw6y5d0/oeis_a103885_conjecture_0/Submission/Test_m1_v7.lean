import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P : Polynomial ℝ := 5 * X^2 - 5 * X + 1

lemma coeff_P_above (N : ℕ) (hN : 2 < N) : P.coeff N = 0 := by
  unfold P
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have h1 : N ≠ 2 := by omega
  have h2 : 2 ≠ N := by omega
  have h3 : N ≠ 1 := by omega
  have h4 : 1 ≠ N := by omega
  have h5 : N ≠ 0 := by omega
  have h6 : 0 ≠ N := by omega
  simp [h1, h2, h3, h4, h5, h6]
