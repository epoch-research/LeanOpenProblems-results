import Submission.Spec
open Nat BigOperators Int

theorem A092243_4_eq : A092243 4 = 2 := by
  dsimp [A092243, Finset.sum]
  -- Can we decide this?
  sorry
