import Mathlib
open Matrix Nat

lemma p0 : Nat.nth Nat.Prime 0 = 2 := by
  -- Can we prove this without sorry?
  exact rfl -- No, it's noncomputable.
