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

def F (X : Prop) : Prop := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

def decomp : Bad → (Prop → Bad)
| Bad.mk2 => fun _ => Bad.mk2
| Bad.mk1 f => f

theorem decomp_mk1 (f : Prop → Bad) : decomp (Bad.mk1 f) = f := rfl

noncomputable def F_bad (X : Prop) : Bad := inj (F X)

noncomputable def U : Bad := Bad.mk1 F_bad

noncomputable def G (T : (Bad → Prop) → Prop) (X : Prop) : F X :=
  fun f p => T (fun x => p (f (fun q => Bad_to_Prop_param (decomp x (F X)) q)))

noncomputable def τ (T : (Bad → Prop) → Prop) : Bad :=
  Bad.mk1 (fun X => inj (G T X))

noncomputable def σ (S : Bad) : (Bad → Prop) → Prop :=
  fun T => T (fun x => Bad_to_Prop_param (decomp S (F (Bad_to_Prop_param x True))) True)




