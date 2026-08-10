import Mathlib
open Nat
lemma odd_test_3 (k : ℤ) (h : ((2 * k : ℤ) : ZMod 2) = 1) : False := by push_cast at h; have h_zero : ∀ (y : ZMod 2), y + y = 0 := by decide; rw [h_zero] at h; contradiction
