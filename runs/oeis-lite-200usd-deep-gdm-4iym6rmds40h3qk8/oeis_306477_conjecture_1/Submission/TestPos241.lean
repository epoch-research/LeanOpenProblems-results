open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def inj_prop (F : (Prop → Prop) → T) : T :=
  T.mk (fun X =>
    if h : ∃ (f : Prop → Prop), X = { g : Prop → Prop // g = f } then
      F (Classical.choose h)
    else
      T.base
  )

noncomputable def proj_prop (t : T) : (Prop → Prop) → T :=
  fun f => proj t ({ g : Prop → Prop // g = f })

theorem proj_inj_prop (F : (Prop → Prop) → T) : proj_prop (inj_prop F) = F := by
  ext f
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (f' : Prop → Prop), { g : Prop → Prop // g = f } = { g : Prop → Prop // g = f' } := ⟨f, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec : { g // g = f } = { g // g = choose h_ex }
  generalize h_choose : Classical.choose h_ex = f' at *
  -- Now h_spec : { g // g = f } = { g // g = f' }
  -- and we want to show: F f' = F f.
  -- This follows if f = f'.
  let val1 : { g // g = f } := ⟨f, rfl⟩
  let val2 : { g // g = f' } := cast h_spec val1
  have h_eq : val2.val = f' := val2.property
  have h_cast : val2.val = f := by
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
  have h_final : f' = f := by
    rw [← h_eq, h_cast]
  rw [h_final]
