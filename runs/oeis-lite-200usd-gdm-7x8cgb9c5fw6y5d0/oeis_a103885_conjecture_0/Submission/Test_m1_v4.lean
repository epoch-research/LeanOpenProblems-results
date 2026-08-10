import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P : Polynomial ℝ := 5 * X^2 - 5 * X + 1

lemma coeff_P_above (N : ℕ) (hN : 2 < N) : P.coeff N = 0 := by
  unfold P
  simp [coeff_add, coeff_sub, coeff_X_pow]
  -- Let's see if we can simplify further or if it's already done
