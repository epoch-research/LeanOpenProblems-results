import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

-- We want the return type of g to be some Prop.
-- Let's define g A : Prop
def g (A : Prop) : Prop := (A → P) → P

theorem r_compat (A B : Prop) (h : r P A B) : g P A = g P B := by
  dsimp [r] at h
  rcases h with h_iff | hP
  · apply propext
    dsimp [g]
    constructor
    · intro h1 h2
      exact h1 (fun hA ↦ h2 (h_iff.mpr hA))
    · intro h1 h2
      exact h1 (fun hB ↦ h2 (h_iff.mp hB))
  · apply propext
    dsimp [g]
    constructor
    · intro _ _
      exact hP
    · intro _ _
      exact hP

def F : Quot (r P) → Prop := Quot.lift (g P) (r_compat P)

-- Now we define a function from Q P to Prop using Nonempty.rec!
def F_Q (x : Q P) : Prop := @Nonempty.rec (Quot (r P)) (fun _ ↦ Prop) (F P) x
