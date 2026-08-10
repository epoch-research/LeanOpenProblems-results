import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Polynomial

theorem test_apery_1 : Irreducible (apery_poly 1) := by
  dsimp [apery_poly]
  -- apery_poly 1 is C 1 * X^0 + C 2 * X^1?
  -- Let's see what it simplifies to
  sorry
