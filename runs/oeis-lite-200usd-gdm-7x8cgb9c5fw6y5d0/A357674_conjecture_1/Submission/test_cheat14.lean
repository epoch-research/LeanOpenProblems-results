import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

variable (p : Type) (F : Quot (r P) → p)

theorem test_eq : F (Quot.mk (r P) True) = F (Quot.mk (r P) False) := by
  have h : Nonempty.elim (el1 P) F = Nonempty.elim (el2 P) F := by
    rw [eq_of_Q]
  exact h
