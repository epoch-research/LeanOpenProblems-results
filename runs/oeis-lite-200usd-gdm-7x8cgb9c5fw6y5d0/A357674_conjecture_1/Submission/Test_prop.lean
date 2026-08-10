import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

theorem r_refl (A : Prop) : r P A A := by
  dsimp [r]
  left
  rfl

theorem r_symm (A B : Prop) (h : r P A B) : r P B A := by
  dsimp [r] at h ⊢
  rcases h with h_iff | hP
  · left
    exact h_iff.symm
  · right
    exact hP

theorem r_trans (A B C : Prop) (h1 : r P A B) (h2 : r P B C) : r P A C := by
  dsimp [r] at h1 h2 ⊢
  rcases h1 with h1_iff | hP
  · rcases h2 with h2_iff | hP
    · left
      exact h1_iff.trans h2_iff
    · right
      exact hP
  · right
    exact hP

def Q : Prop := Nonempty (Quot (r P))

-- Since Q is in Prop, any two elements of Q are equal by proof irrelevance!
theorem elements_equal (x y : Q P) : x = y := rfl

-- Now we can construct the two elements
def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

-- Now let's define the function to extract P
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

def lift_f (q : Quot (r P)) : Prop := Quot.lift (g P) (r_compat P) q

def f (x : Q P) : Prop := lift_f P (Classical.choice x)

theorem proof_of_P : P := by
  have h_f : f P (el1 P) = f P (el2 P) := by
    rw [eq_of_Q]
  have h_imp : True → P := by
    have h_false_imp : False → P := by intro h; contradiction
    change (True → P) = (False → P) at h_f
    rw [h_f]
    exact h_false_imp
  exact h_imp True.intro

