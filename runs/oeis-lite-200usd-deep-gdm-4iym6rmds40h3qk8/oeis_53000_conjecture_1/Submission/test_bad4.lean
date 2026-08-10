inductive Bad4 : Type 1
| mk1 : (Type 0 → Bad4) → Bad4
| base : Bad4

open Classical

def Bad4_to_Prop : Bad4 → Type 0 → Prop
| Bad4.base, _ => False
| Bad4.mk1 f, X => ¬ (Bad4_to_Prop (f X) X)

noncomputable def inj (X : Type 0) : Bad4 :=
  if Nonempty X then Bad4.mk1 (fun _ => Bad4.base) else Bad4.base

theorem Bad4_to_Prop_inj (X : Type 0) (Y : Type 0) : Bad4_to_Prop (inj X) Y ↔ Nonempty X := by
  by_cases h : Nonempty X
  · have h_inj : inj X = Bad4.mk1 (fun _ => Bad4.base) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [Bad4_to_Prop]
    constructor
    · intro _
      exact h
    · intro _
      exact id
  · have h_inj : inj X = Bad4.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [Bad4_to_Prop]
    constructor
    · intro h2
      contradiction
    · intro h2
      contradiction

def P : Bad4 → Prop
| Bad4.base => False
| Bad4.mk1 f => ¬ (P (f (PLift (P (Bad4.mk1 f)))))

