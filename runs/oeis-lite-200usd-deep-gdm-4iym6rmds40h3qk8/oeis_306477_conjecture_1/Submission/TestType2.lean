open Classical

inductive T : Type 2 where
  | base : T
  | mk : (Type 1 → T) → T

def proj : T → (Type 1 → T)
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

noncomputable def inj_T (F : (T → Prop) → Prop) : T :=
  T.mk (fun X =>
    if h : ∃ P : T → Prop, X = { f : T → Prop // f = P } then
      prop_to_T (F (Classical.choose h))
    else
      T.base
  )

noncomputable def proj_T (t : T) : (T → Prop) → Prop :=
  fun P => T_to_prop (proj t { f : T → Prop // f = P })

theorem Subtype_inj (P1 P2 : T → Prop) (h : { f : T → Prop // f = P1 } = { f : T → Prop // f = P2 }) : P1 = P2 := by
  have h1 : P1 ∈ { f : T → Prop // f = P1 } := ⟨rfl⟩
  -- wait, { f // f = P1 } is a type, so P1 is not in it, but ⟨P1, rfl⟩ has type { f // f = P1 }.
  let val : { f : T → Prop // f = P1 } := ⟨P1, rfl⟩
  let val2 : { f : T → Prop // f = P2 } := cast h val
  exact val2.property

theorem proj_inj_T (F : (T → Prop) → Prop) : proj_T (inj_T F) = F := by
  ext P
  dsimp [proj_T, inj_T, proj]
  have h_ex : ∃ P', { f : T → Prop // f = P } = { f : T → Prop // f = P' } := ⟨P, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : P = Classical.choose h_ex := Subtype_inj P (Classical.choose h_ex) h_spec
  generalize Classical.choose h_ex = Q at *
  cases h_eq
  rw [propext (T_to_prop_to_T (F P))]
