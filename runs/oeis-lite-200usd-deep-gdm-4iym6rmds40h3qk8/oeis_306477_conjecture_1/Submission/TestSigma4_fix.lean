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
  constructor
  · intro h
    rcases h with ⟨x, h_eq⟩
    generalize h_spec = eq_proof
    cases eq_proof
    rcases x with ⟨P', ⟨h_FP'⟩⟩
    dsimp at h_eq
    rw [← h_eq]
    exact h_FP'
  · intro h
    refine ⟨⟨P, ⟨h⟩⟩, ?_⟩
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
