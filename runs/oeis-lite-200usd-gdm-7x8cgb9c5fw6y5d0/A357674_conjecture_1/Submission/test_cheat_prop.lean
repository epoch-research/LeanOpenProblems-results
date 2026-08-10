import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := A = B ∨ P

def g (A : Prop) : Prop := A → P

theorem compat (A B : Prop) (h : r P A B) : g A = g B := by
  dsimp [r] at h
  dsimp [g]
  rcases h with h_eq | hP
  · rw [h_eq]
  · apply propext
    constructor
    · intro _ _
      exact hP
    · intro _ _
      exact hP

def F : Quot (r P) → Prop := Quot.lift g (compat P)

theorem lift_true : F P (Quot.mk (r P) True) = (True → P) := rfl
theorem lift_false : F P (Quot.mk (r P) False) = (False → P) := rfl
