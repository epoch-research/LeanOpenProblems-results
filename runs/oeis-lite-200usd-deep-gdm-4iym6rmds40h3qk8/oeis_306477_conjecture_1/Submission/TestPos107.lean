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
  have h1 : p1 = p2 := by
    -- PLift p1 = PLift p2 implies their constructor elements are isomorphic, but wait:
    -- by propext, we can prove p1 ↔ p2.
    constructor
    · intro hp1
      let val : PLift p2 := cast h (PLift.up hp1)
      exact val.down
    · intro hp2
      let val : PLift p1 := cast h.symm (PLift.up hp2)
      exact val.down
  exact h1

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : p = Classical.choose h_ex := PLift_inj p (Classical.choose h_ex) h_spec
  -- We want to prove f (choose h_ex) = f p.
  -- Since choose h_ex and p are equal by h_eq, we can rewrite using h_eq.symm!
  have h_eq_symm := h_eq.symm
  -- Let's use h_eq_symm to change choose h_ex to p.
  -- We can't use rw [h_eq_symm] directly because choose h_ex's type depends on h_ex.
  -- But we can rewrite inside f!
  -- Actually, h_eq is: p = choose h_ex.
  -- So we can do:
  congr
