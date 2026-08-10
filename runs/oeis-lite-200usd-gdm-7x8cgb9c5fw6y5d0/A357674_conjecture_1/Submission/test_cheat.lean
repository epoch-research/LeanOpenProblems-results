import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)
noncomputable def val2 : Quot (r P) := Classical.choice (el2 P)

theorem val_eq : val1 P = val2 P := rfl
