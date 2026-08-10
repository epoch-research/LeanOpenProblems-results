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
  constructor
  · intro h
    rcases h with ⟨x, h_eq⟩
    -- x : inj F
    -- h_eq : (cast h_spec x).fst = P
    -- We want to prove F P.
    -- Let's do cases on h_spec BEFORE unfolding inj!
    generalize h_spec = eq_proof
    cases eq_proof
    -- Now choose h_ex is replaced by F, and eq_proof is rfl!
    -- So cast rfl x is just x!
    -- So h_eq is x.fst = P!
    dsimp at h_eq
    -- x : inj F => x is ⟨x.fst, x.snd⟩
    rcases x with ⟨P', ⟨h_FP'⟩⟩
    dsimp at h_eq
    rw [← h_eq]
    exact h_FP'
  · intro h
    let x : inj F := ⟨P, ⟨h⟩⟩
    use x
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
