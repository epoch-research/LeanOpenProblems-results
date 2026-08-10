import Mathlib

def P : Prop := 1 + 1 = 3

def R (b1 b2 : Bool) : Prop :=
  b1 = b2 ∨ (b1 = true ∧ b2 = false ∧ P)

theorem R_sound : Quot.mk R true = Quot.mk R false := by
  sorry
