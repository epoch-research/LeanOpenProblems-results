import FormalConjectures.Util.ProblemImports
import Submission.Spec

open A052709_Conjecture

#check oeis_52709_conjecture_0
example : [1, 1] ∈ sequences_counted_by_A052709 3 := by decide


theorem test_1 : A052709 1 = Fintype.card (sequences_counted_by_A052709 1) := by
  decide

theorem test_2 : A052709 2 = Fintype.card (sequences_counted_by_A052709 2) := by
  decide

theorem test_3 : A052709 3 = Fintype.card (sequences_counted_by_A052709 3) := by
  decide

theorem test_4 : A052709 4 = Fintype.card (sequences_counted_by_A052709 4) := by
  decide
