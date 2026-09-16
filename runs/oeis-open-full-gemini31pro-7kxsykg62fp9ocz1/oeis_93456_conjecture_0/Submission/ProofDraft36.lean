import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma algebra_ineq (p M x : ℕ) (hp5 : 5 ≤ p) (hx : M - p + 3 ≤ x) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * x := by
  zify [show p * p ≤ p * M by nlinarith, show p ≤ M by nlinarith]
  have hz : (M : ℤ) - (p : ℤ) + 3 ≤ (x : ℤ) := by
    zify [show p ≤ M by nlinarith] at hx
    exact hx
  nlinarith
