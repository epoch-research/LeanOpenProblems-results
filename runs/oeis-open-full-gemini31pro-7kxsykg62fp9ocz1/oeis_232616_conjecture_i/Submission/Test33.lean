import Mathlib
import Submission.Spec
open Nat Finset Set

lemma not_a232616_prop_1_0 : ¬ A232616_prop 1 0 := by
  intro h
  dsimp [A232616_prop] at h
  have h1 : (0 : ZMod 1) ∈ (univ : Finset (ZMod 1)) := mem_univ 0
  rw [h] at h1
  simp at h1
