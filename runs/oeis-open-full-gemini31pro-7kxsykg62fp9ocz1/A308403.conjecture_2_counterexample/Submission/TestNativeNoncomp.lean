import Mathlib

noncomputable def S (n : ℕ) : ℕ := n

theorem test : S 0 = 0 := by native_decide
