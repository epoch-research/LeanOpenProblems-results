inductive Bad : Type 1
| mk1 : (Prop → Bad) → Bad
| mk2 : Bad

open Classical

def Bad_to_Prop_param : Bad → Prop → Prop
| Bad.mk2, _ => False
| Bad.mk1 f, p => ¬ (Bad_to_Prop_param (f p) p)

noncomputable def inj (p : Prop) : Bad :=
  if p then Bad.mk1 (fun _ => Bad.mk2) else Bad.mk2

theorem Bad_to_Prop_param_inj (p : Prop) (q : Prop) : Bad_to_Prop_param (inj p) q ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Bad.mk1 (fun _ => Bad.mk2) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [Bad_to_Prop_param]
    constructor
    · intro _
      exact h
    · intro _
      exact id
  · have h_inj : inj p = Bad.mk2 := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [Bad_to_Prop_param]
    constructor
    · intro h2
      contradiction
    · intro h2
      contradiction

noncomputable def U : Bad := Bad.mk1 (fun p => inj p)

theorem U_step (p : Prop) : Bad_to_Prop_param U p ↔ ¬ p := by
  have h1 : U = Bad.mk1 (fun p => inj p) := rfl
  rw [h1]
  dsimp [Bad_to_Prop_param]
  rw [Bad_to_Prop_param_inj]
