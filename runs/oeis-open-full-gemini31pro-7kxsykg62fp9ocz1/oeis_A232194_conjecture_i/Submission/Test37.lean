import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem test_0 : (0 > 2 → a 0 > 0) ∧ (a 0 = 1 ↔ 0 = 3 ∨ 0 = 4 ∨ 0 = 6 ∨ 0 = 20 ∨ 0 = 24) := by
  decide

theorem test_1 : (1 > 2 → a 1 > 0) ∧ (a 1 = 1 ↔ 1 = 3 ∨ 1 = 4 ∨ 1 = 6 ∨ 1 = 20 ∨ 1 = 24) := by
  decide

theorem test_2 : (2 > 2 → a 2 > 0) ∧ (a 2 = 1 ↔ 2 = 3 ∨ 2 = 4 ∨ 2 = 6 ∨ 2 = 20 ∨ 2 = 24) := by
  decide
