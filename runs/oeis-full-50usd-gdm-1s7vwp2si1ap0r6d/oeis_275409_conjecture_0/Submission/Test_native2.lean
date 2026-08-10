import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

theorem test_native : a_computable 1 = 2 := by
  native_decide
