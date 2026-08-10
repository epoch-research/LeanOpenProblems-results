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
  have h1 : p1 ↔ PLift p1 := PLift.equiv.symm
  have h2 : p2 ↔ PLift p2 := PLift.equiv.symm
  rw [h1, h2, h]

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec is: PLift p = PLift (choose h_ex)
  -- By PLift_inj, this means p = choose h_ex!
  have h_eq : p = Classical.choose h_ex := PLift_inj p (Classical.choose h_ex) h_spec
  -- Since p = choose h_ex, f (choose h_ex) is equal to f p!
  -- Let's do cases on h_eq!
  subst h_eq
  rfl
