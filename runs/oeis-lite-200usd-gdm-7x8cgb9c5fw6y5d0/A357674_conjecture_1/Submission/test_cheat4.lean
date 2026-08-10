import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)

theorem test_choice : val1 P = Quot.mk (r P) True := rfl
