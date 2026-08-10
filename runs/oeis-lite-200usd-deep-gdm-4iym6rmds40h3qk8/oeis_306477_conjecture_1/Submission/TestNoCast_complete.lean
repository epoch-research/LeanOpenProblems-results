open Classical

def inj (F : (Prop → Prop) → Prop) : Type :=
  (P : Prop → Prop) → (F P → False)

noncomputable def proj (X : Type) (P : Prop → Prop) : Prop :=
  if h : ∃ (F : (Prop → Prop) → Prop), X = inj F then
    let F' := Classical.choose h
    have h_spec : X = inj F' := Classical.choose_spec h
    -- We want to return (inj F' P) → False
    -- Since h_spec : X = inj F', we can rewrite inj F' as X!
    -- So we return: (cast h_spec.symm ...)?
    -- No, (inj F' P) is a Prop. We can just write:
    (inj F' P) → False
  else
    False

theorem proj_inj (F : (Prop → Prop) → Prop) : proj (inj F) = F := by
  ext P
  dsimp [proj]
  have h_ex : ∃ (F' : (Prop → Prop) → Prop), inj F = inj F' := ⟨F, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec : inj F = inj (Classical.choose h_ex)
  -- We want to prove: (inj (Classical.choose h_ex) P → False) ↔ F P
  -- Since h_spec : inj F = inj (Classical.choose h_ex)
  -- We can rewrite using h_spec.symm!
  rw [← h_spec]
  -- Now the goal is: (inj F P → False) ↔ F P
  -- Since inj F P is: F P → False
  -- The goal is: ((F P → False) → False) ↔ F P
  constructor
  · intro h
    by_contra h_not
    exact h h_not
  · intro h h_not
    exact h_not h
