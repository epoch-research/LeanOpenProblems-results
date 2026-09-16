import Mathlib

open Nat

noncomputable def p0 : ℕ := Nat.nth Nat.Prime 0

-- Can we prove p0 = 2?
lemma p0_is_2 : p0 = 2 := by
  sorry
