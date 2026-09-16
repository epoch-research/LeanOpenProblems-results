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

lemma not_a232616_prop_1_0 : ¬ A232616_prop 1 0 := by
  intro h
  dsimp [A232616_prop] at h
  have h1 : (0 : ZMod 1) ∈ (univ : Finset (ZMod 1)) := mem_univ 0
  rw [h] at h1
  simp at h1

-- Can we prove A232616 1 = 1?
-- A232616 1 = sInf { m | A232616_prop 1 m }
