import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def P : Polynomial ℝ := 5 * X^2 - 5 * X + 1
def Q : Polynomial ℝ := 220 * X^2 - 136 * X + 12

lemma degP : P.degree = (2 : ℕ) := by
  unfold P
  compute_degree!
