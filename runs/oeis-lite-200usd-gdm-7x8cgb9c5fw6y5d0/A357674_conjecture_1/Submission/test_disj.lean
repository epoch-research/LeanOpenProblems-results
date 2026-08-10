import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

noncomputable def val1 : Quot (r P) := Classical.choice (el1 P)
noncomputable def val2 : Quot (r P) := Classical.choice (el2 P)

theorem val_eq : val1 P = val2 P := by
  have h : Classical.choice (el1 P) = Classical.choice (el2 P) := by
    rw [eq_of_Q]
  exact h

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

noncomputable def F : Quot (r P) → Prop := Quot.lift (g P) (r_compat P)

theorem F_val_cases : F P (val1 P) = (True → P) ∨ F P (val1 P) = (False → P) := by
  have h_ind : ∀ (q : Quot (r P)), F P q = (True → P) ∨ F P q = (False → P) := by
    apply Quot.ind
    intro A
    by_cases hA : A
    · left
      have h_eq : A = True := propext ⟨fun _ => True.intro, fun _ => hA⟩
      rw [h_eq]
      rfl
    · right
      have h_eq : A = False := propext ⟨fun h => hA h, fun h => h.elim⟩
      rw [h_eq]
      rfl
  exact h_ind (val1 P)
