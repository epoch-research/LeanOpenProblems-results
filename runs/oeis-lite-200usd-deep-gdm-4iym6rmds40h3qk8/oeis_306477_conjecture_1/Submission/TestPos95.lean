open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Let's define the bijection between Prop → T and Type → T.
noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X =>
    if h : ∃ (p : Prop), X = p then
      f (Classical.choose h)
    else
      T.base
  )

noncomputable def proj_prop (t : T) : Prop → T :=
  fun p => proj t p

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  -- proj (inj_prop f) p
  -- = if h : ∃ (p' : Prop), p = p' then f (Classical.choose h) else T.base
  have h_ex : ∃ (p' : Prop), (p : Type) = p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  -- Now we have: f (Classical.choose h_ex)
  -- We want to prove this is f p.
  -- Since choose h_ex has type Prop, and its specification says p = choose h_ex.
  -- So by equality of types, they are equal, so by f being a function, the values are equal.
  have h_eq : p = Classical.choose h_ex := by
    have h_spec := Classical.choose_spec h_ex
    exact h_spec
  rw [h_eq]
