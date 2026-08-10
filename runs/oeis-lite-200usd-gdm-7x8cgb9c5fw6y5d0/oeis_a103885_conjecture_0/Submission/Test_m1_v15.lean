import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def Q : Polynomial ℝ := 220 * X^2 - 136 * X + 12

lemma coeff_Q_above (N : ℕ) (hN : 2 < N) : Q.coeff N = 0 := by
  unfold Q
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have h1 : N ≠ 2 := by omega
  have h4 : 1 ≠ N := by omega
  have h5 : N ≠ 0 := by omega
  simp [h1, h4]
  rcases Nat.exists_eq_succ_of_ne_zero h5 with ⟨d, rfl⟩
  exact coeff_ofNat_succ 12 d
