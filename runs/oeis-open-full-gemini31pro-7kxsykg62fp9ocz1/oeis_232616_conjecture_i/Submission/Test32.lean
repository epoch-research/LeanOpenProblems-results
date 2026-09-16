import Mathlib
import Submission.Spec
open Nat Finset Set

lemma a232616_prop_1_1 : A232616_prop 1 1 := by
  dsimp [A232616_prop]
  ext x
  simp
  constructor
  · intro _
    exact Subsingleton.elim x 0
  · intro _
    exact Subsingleton.elim x default
