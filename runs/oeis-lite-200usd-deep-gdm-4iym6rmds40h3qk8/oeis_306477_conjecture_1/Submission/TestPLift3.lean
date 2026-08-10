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

noncomputable def inj_P (f : (Prop → Prop) → Prop) : T :=
  T.mk (fun X => prop_to_T (∃ P, X = { y : Prop → Prop // y = P } ∧ f P))

noncomputable def proj_P (t : T) : (Prop → Prop) → Prop :=
  fun P => T_to_prop (proj t { y : Prop → Prop // y = P })

theorem proj_inj_P (f : (Prop → Prop) → Prop) : proj_P (inj_P f) = f := by
  ext P
  dsimp [proj_P, inj_P, proj]
  rw [propext (T_to_prop_to_T _)]
  constructor
  · intro h
    rcases h with ⟨P', h_eq, h_fP'⟩
    generalize h_eq = eq_proof
    cases eq_proof
    exact h_fP'
  · intro h
    exact ⟨P, rfl, h⟩
