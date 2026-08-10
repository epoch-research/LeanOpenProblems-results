import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def f (b : Bool) : Prop := if b then True else P

theorem compat (a b : Bool) (h : r a b) : f P a = f P b := by
  dsimp [r] at h
  cases a <;> cases b <;> dsimp [f]
  · rfl
  · apply propext
    constructor
    · intro _
      exact h
    · intro _
      exact True.intro
  · apply propext
    constructor
    · intro _
      exact True.intro
    · intro _
      exact h
  · rfl

def F : Quot (r P) → Prop := Quot.lift (f P) (compat P)
