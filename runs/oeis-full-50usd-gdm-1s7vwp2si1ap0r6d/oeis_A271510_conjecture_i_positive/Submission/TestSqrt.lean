
import FormalConjectures.Util.ProblemImports

open Nat

lemma le_of_sq_identity (y z : ℕ) (h : y ≥ 1 ∨ z ≥ 1) :
    y ≤ 2 * y ^ 2 + 4 * z ^ 2 - 1 := by
  rcases h with hy | hz
  · have : 2 * y ^ 2 ≥ y + 1 := by nlinarith
    omega
  · by_cases hy : y ≥ 1
    · have : 2 * y ^ 2 ≥ y + 1 := by nlinarith
      omega
    · have hy0 : y = 0 := by omega
      subst hy0
      have : 4 * z ^ 2 ≥ 4 := by nlinarith
      omega
