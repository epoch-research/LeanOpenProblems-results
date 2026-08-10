import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def g (P : Prop) (b : Bool) : Prop := if b then True else P

theorem compat (P : Prop) (a b : Bool) (h : r P a b) : g P a = g P b := by
  dsimp [g]
  cases a
  · cases b
    · rfl
    · apply propext
      constructor
      · intro _
        exact True.intro
      · intro _
        exact h
  · cases b
    · apply propext
      constructor
      · intro _
        exact h
      · intro _
        exact True.intro
    · rfl

def F (P : Prop) : Quot (r P) → Prop := Quot.lift (g P) (compat P)

theorem lift_true : F P (Quot.mk (r P) true) = True := rfl
theorem lift_false : F P (Quot.mk (r P) false) = P := rfl
