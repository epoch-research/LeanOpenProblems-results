import Mathlib

variable (P : Prop)

def r (a b : Bool) : Prop := P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) true)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) false)

theorem eq_of_Q : el1 P = el2 P := rfl

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)
noncomputable def val2 : Quot (r P) := Classical.choice (el2 P)

theorem val_eq : val1 P = val2 P := by
  have h : Classical.choice (el1 P) = Classical.choice (el2 P) := by
    rw [eq_of_Q]
  exact h

def g (b : Bool) : Prop := if b then True else P

theorem compat (a b : Bool) (h : r P a b) : g P a = g P b := by
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

noncomputable def F : Quot (r P) → Prop := Quot.lift (g P) (compat P)

theorem F_val1 : F P (val1 P) = True := by
  dsimp [val1]
  -- Classical.choice (Nonempty.intro X) is equal to X? No, not definitionally.
  -- But we can show it using something?
  sorry
