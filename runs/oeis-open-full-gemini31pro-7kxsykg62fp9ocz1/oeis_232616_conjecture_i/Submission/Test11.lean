import Submission.Spec
open Nat Finset Set

lemma A232616_prop_1_1 : A232616_prop 1 1 := by
  dsimp [A232616_prop]
  ext x
  simp
  -- ZMod 1 has only one element, which is 0
  sorry

