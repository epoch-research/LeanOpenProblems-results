import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def el1 : Nonempty (Quot (r P)) := Nonempty.intro (Quot.mk (r P) true)
def el2 : Nonempty (Quot (r P)) := Nonempty.intro (Quot.mk (r P) false)

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)
noncomputable def val2 : Quot (r P) := Classical.choice (el2 P)

theorem val_eq : val1 P = val2 P := rfl
