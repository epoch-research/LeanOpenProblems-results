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

-- Now we define:
--   inj_P : (Prop → Prop) → T
--   proj_P : T → (Prop → Prop)
noncomputable def inj_P (f : Prop → Prop) : T :=
  inj_prop (fun p => prop_to_T (f p))

noncomputable def proj_P (t : T) : Prop → Prop :=
  fun p => T_to_prop (proj_prop t p)

theorem proj_inj_P (f : Prop → Prop) : proj_P (inj_P f) = f := by
  ext p
  dsimp [proj_P, inj_P]
  rw [proj_inj_prop]
  rw [propext (T_to_prop_to_T (f p))]
