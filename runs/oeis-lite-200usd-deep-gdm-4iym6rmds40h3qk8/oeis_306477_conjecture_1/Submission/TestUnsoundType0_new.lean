open Classical

inductive T : Type where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

theorem proj_mk (f : Type → T) : proj (T.mk f) = f := rfl

noncomputable def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

theorem T_to_prop_to_T (p : Prop) : T_to_prop (prop_to_T p) = p := by
  dsimp [prop_to_T, T_to_prop]
  by_cases h : p
  · rw [if_pos h]
    exact propext ⟨fun _ => h, fun _ => trivial⟩
  · rw [if_neg h]
    exact propext ⟨False.elim, fun hp => h hp⟩

noncomputable def f_T {α : Type} [Inhabited α] (Y : Type) : α :=
  if h : Nonempty Y then
    (Classical.choice h).val
  else
    default

theorem subtype_eq_inj {α : Type} [Inhabited α] (P1 P2 : α) (h : { y : α // y = P1 } = { y : α // y = P2 }) : P1 = P2 := by
  have h_eq : f_T { y : α // y = P1 } = f_T { y : α // y = P2 } := by
    rw [h]
  have h_P1 : f_T { y : α // y = P1 } = P1 := by
    dsimp [f_T]
    have h_ne : Nonempty { y : α // y = P1 } := ⟨⟨P1, rfl⟩⟩
    rw [dif_pos h_ne]
    exact (Classical.choice h_ne).property
  have h_P2 : f_T { y : α // y = P2 } = P2 := by
    dsimp [f_T]
    have h_ne : Nonempty { y : α // y = P2 } := ⟨⟨P2, rfl⟩⟩
    rw [dif_pos h_ne]
    exact (Classical.choice h_ne).property
  rw [h_P1, h_P2] at h_eq
  exact h_eq

noncomputable def inj_T (F : (T → Prop) → Prop) : T :=
  T.mk (fun X =>
    if h : ∃ P : T → Prop, X = { f : T → Prop // f = P } then
      prop_to_T (F (Classical.choose h))
    else
      T.base
  )

noncomputable def proj_T (t : T) : (T → Prop) → Prop :=
  fun P => T_to_prop (proj t { f : T → Prop // f = P })

theorem proj_inj_T (F : (T → Prop) → Prop) : proj_T (inj_T F) = F := by
  ext P
  dsimp [proj_T, inj_T, proj]
  have h_ex : ∃ P', { f : T → Prop // f = P } = { f : T → Prop // f = P' } := ⟨P, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : P = Classical.choose h_ex := subtype_eq_inj P (Classical.choose h_ex) h_spec
  generalize Classical.choose h_ex = Q at *
  cases h_eq
  rw [T_to_prop_to_T]
