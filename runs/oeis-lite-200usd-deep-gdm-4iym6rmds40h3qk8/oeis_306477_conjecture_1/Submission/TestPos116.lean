open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

theorem T_to_prop_to_T (p : Prop) : T_to_prop (prop_to_T p) ↔ p := by
  dsimp [prop_to_T, T_to_prop]
  by_cases h : p
  · rw [if_pos h]
    constructor
    · intro _
      exact h
    · intro _
      trivial
  · rw [if_neg h]
    constructor
    · intro h_contra
      exact False.elim h_contra
    · intro hp
      exact False.elim (h hp)

-- Let's define:
--   inj_F : ((Type → Prop) → Prop) → T
--   proj_F : T → ((Type → Prop) → Prop)
noncomputable def inj_F (F : (Type → Prop) → Prop) : T :=
  T.mk (fun X => prop_to_T (F (fun Y => X = Y)))

noncomputable def proj_F (t : T) : (Type → Prop) → Prop :=
  fun P => T_to_prop (proj t (Classical.choose (by
    -- we want to find X such that P = (fun Y => X = Y)
    -- This is only possible if P is of the form (fun Y => X = Y) (i.e. P is a singleton).
    -- But wait! Hurkens' paradox on U requires an injection from ((U → Prop) → Prop) to U.
    -- Here U is Type.
    -- So we need an injection from ((Type → Prop) → Prop) to Type!
    -- But Type is a Type, not a term.
    sorry
  )))
