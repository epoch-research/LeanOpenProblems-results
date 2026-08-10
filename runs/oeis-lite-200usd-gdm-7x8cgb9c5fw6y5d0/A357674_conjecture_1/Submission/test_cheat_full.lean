import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def el1 : Nonempty (Quot (r P)) := Nonempty.intro (Quot.mk (r P) true)
def el2 : Nonempty (Quot (r P)) := Nonempty.intro (Quot.mk (r P) false)

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)
noncomputable def val2 : Quot (r P) := Classical.choice (el2 P)

theorem val_eq : val1 P = val2 P := rfl

def g (P : Prop) (b : Bool) : Prop := if b then True else P

theorem compat (P : Prop) (a b : Bool) (h : r P a b) : g P a = g P b := by
  dsimp [g]
  cases a
  · cases b
    · rfl
    · dsimp [r] at h
      apply propext
      constructor
      · intro _
        exact True.intro
      · intro _
        exact h
  · cases b
    · dsimp [r] at h
      apply propext
      constructor
      · intro _
        exact h
      · intro _
        exact True.intro
    · rfl

noncomputable def F (P : Prop) : Quot (r P) → Prop := Quot.lift (g P) (compat P)

theorem F_val_eq : F P (val1 P) = F P (val2 P) := by
  rw [val_eq]
