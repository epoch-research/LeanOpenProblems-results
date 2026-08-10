import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def Q : Polynomial ℝ := 220 * X^2 - 136 * X + 12

lemma coeff_Q_above (N : ℕ) (hN : 2 < N) : Q.coeff N = 0 := by
  unfold Q
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0) with ⟨d, rfl⟩
  rfl
