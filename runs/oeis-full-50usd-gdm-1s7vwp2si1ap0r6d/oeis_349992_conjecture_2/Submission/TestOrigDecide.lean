import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem test_orig_1 : generalized_A349992 1 1 11 12 1 > 0 := by
  unfold generalized_A349992
  simp
  decide

theorem test_orig_2 : generalized_A349992 1 1 11 12 2 > 0 := by
  unfold generalized_A349992
  simp
  decide
