open Classical

def inj (F : (Prop → Prop) → Prop) : Type :=
  Σ (P : Prop → Prop), PLift (F P)

noncomputable def proj (X : Type) (P : Prop → Prop) : Prop :=
  if h : ∃ (F : (Prop → Prop) → Prop), X = inj F then
    let h_eq := Classical.choose_spec h
    ∃ (x : X), (cast h_eq x).fst = P
  else
    False

theorem proj_inj (F : (Prop → Prop) → Prop) : proj (inj F) = F := by
  ext P
  dsimp [proj]
  have h_ex : ∃ (F' : (Prop → Prop) → Prop), inj F = inj F' := ⟨F, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec : inj F = inj (choose h_ex)
  generalize h_spec = eq_proof
  cases eq_proof
  -- Now the goal is: (∃ x, x.fst = P) ↔ F P
  constructor
  · intro h
    cases h with
    | intro x h_eq =>
      cases x with
      | mk P' val =>
        dsimp at h_eq
        rw [← h_eq]
        exact val.down
  · intro h
    let x : inj F := ⟨P, ⟨h⟩⟩
    exact ⟨x, rfl⟩
