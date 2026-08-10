import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def g2 (A : Prop) : Prop := (A = True → P) ∨ (A = False → P)

theorem r_compat2 (A B : Prop) (h : r P A B) : g2 P A = g2 P B := by
  dsimp [g2]
  rcases h with h_iff | hP
  · have h_eq : A = B := propext h_iff
    rw [h_eq]
  · apply propext
    constructor
    · intro _
      left
      intro _
      exact hP
    · intro _
      left
      intro _
      exact hP
