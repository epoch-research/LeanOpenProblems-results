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

def not_T (t : T) : T :=
  if t = T.base then T.mk (fun _ => T.base) else T.base

theorem not_T_ne (t : T) : not_T t ≠ t := by
  intro h
  dsimp [not_T] at h
  split_ifs at h with h1
  · subst h1
    nomatch h
  · exact h1 h.symm

mutual
  noncomputable def e (p : Prop) : T :=
    inj_prop d

  noncomputable def d (p : Prop) : T :=
    not_T (proj_prop (e p) p)
end
