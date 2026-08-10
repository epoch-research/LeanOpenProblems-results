inductive Bad : Type 1
| mk1 : (Type 0 → Bad) → Bad
| mk2 : Bad

open Classical

def Bad_to_Prop_param : Bad → Type 0 → Prop
| Bad.mk2, _ => False
| Bad.mk1 f, X => ¬ (Bad_to_Prop_param (f X) X)

noncomputable def inj (p : Type 0) : Bad :=
  if Nonempty p then Bad.mk1 (fun _ => Bad.mk2) else Bad.mk2

theorem Bad_to_Prop_param_inj (p : Type 0) (q : Type 0) : Bad_to_Prop_param (inj p) q ↔ Nonempty p := by
  by_cases h : Nonempty p
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

def P : Bad → Prop
| Bad.mk2 => False
| Bad.mk1 f => ¬ (P (f (PLift (P (Bad.mk2)))))


def F (X : Type 0) : Type 0 := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

def decomp : Bad → (Type 0 → Bad)
| Bad.mk2 => fun _ => Bad.mk2
| Bad.mk1 f => f

noncomputable def F_bad (X : Type 0) : Bad := inj (F X)

noncomputable def U : Bad := Bad.mk1 F_bad

noncomputable def G (T : (Bad → Prop) → Prop) (X : Type 0) : F X :=
  fun f p => T (fun x => p (f (fun q => Bad_to_Prop_param (decomp x (F X)) (PLift q))))

noncomputable def τ (T : (Bad → Prop) → Prop) : Bad :=
  Bad.mk1 (fun X => inj (G T X))

noncomputable def σ (S : Bad) : (Bad → Prop) → Prop :=
  fun T => T (fun x => Bad_to_Prop_param (decomp S (F (PLift (Bad_to_Prop_param x (PLift True))))) (PLift True))

