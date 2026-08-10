import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

def g (A : Prop) : Prop := A → P

theorem r_compat (A B : Prop) (h : r P A B) : g P A = g P B := by
  dsimp [r] at h
  rcases h with h_iff | hP
  · apply propext
    dsimp [g]
    constructor
    · intro hA hB
      exact hA (h_iff.mpr hB)
    · intro hB hA
      exact hB (h_iff.mp hA)
  · apply propext
    dsimp [g]
    constructor
    · intro _ _
      exact hP
    · intro _ _
      exact hP

def F : Quot (r P) → Prop := Quot.lift (g P) (r_compat P)

theorem test_eq : F P (Quot.mk (r P) True) = F P (Quot.mk (r P) False) := by
  have h : Nonempty.elim (el1 P) (F P) = Nonempty.elim (el2 P) (F P) := by
    rw [eq_of_Q]
  exact h

theorem prove_P : P := by
  have h_eq : (True → P) = (False → P) := test_eq P
  have h_false_impl : False → P := by
    intro h
    exact h.elim
  rw [h_eq] at h_false_impl
  exact h_false_impl True.intro
