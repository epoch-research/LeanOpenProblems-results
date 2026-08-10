open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X =>
    if h : ∃ (p : Prop), X = PLift p then
      f (Classical.choose h)
    else
      T.base
  )

noncomputable def proj_prop (t : T) : Prop → T :=
  fun p => proj t (PLift p)

theorem PLift_inj (p1 p2 : Prop) (h : PLift p1 = PLift p2) : p1 = p2 := by
  have h1 : p1 ↔ p2 := by
    constructor
    · intro hp1
      let val : PLift p2 := cast h (PLift.up hp1)
      exact val.down
    · intro hp2
      let val : PLift p1 := cast h.symm (PLift.up hp2)
      exact val.down
  exact propext h1

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : p = Classical.choose h_ex := PLift_inj p (Classical.choose h_ex) h_spec
  generalize Classical.choose h_ex = q at *
  cases h_eq
  rfl

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

noncomputable def inj_PP (f : Prop → Prop) : Prop :=
  T_to_prop (inj_prop (fun p => prop_to_T (f p)))

noncomputable def proj_PP (p : Prop) : Prop → Prop :=
  fun q => T_to_prop (proj_prop (prop_to_T p) q)

theorem proj_inj_PP (f : Prop → Prop) : proj_PP (inj_PP f) = f := by
  ext q
  dsimp [proj_PP, inj_PP]
  rw [T_to_prop_to_T]
  rw [proj_inj_prop]
  rw [T_to_prop_to_T]
