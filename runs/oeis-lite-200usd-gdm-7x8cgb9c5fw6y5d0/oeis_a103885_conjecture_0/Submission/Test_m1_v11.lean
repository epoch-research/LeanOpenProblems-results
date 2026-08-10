import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def Q : Polynomial ℝ := 220 * X^2 - 136 * X + 12

lemma coeff_Q_above (N : ℕ) (hN : 2 < N) : Q.coeff N = 0 := by
  unfold Q
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0) with ⟨d, rfl⟩
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one, coeff_ofNat_succ]
  have h1 : d + 1 ≠ 2 := by omega
  have h4 : 1 ≠ d + 1 := by omega
  simp [h1, h4]
