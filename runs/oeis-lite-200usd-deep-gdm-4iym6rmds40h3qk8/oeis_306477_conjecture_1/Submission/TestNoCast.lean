open Classical

def inj (F : (Prop → Prop) → Prop) : Type :=
  (P : Prop → Prop) → (F P → False)

noncomputable def proj (X : Type) (P : Prop → Prop) : Prop :=
  if h : ∃ (F : (Prop → Prop) → Prop), X = inj F then
    -- Here we know X = inj F.
    -- But wait, we still have to do cases on h to get F!
    -- If we do cases on h, we get F' and X = inj F'.
    -- But since we don't have to cast any element of X, does it work?
    -- Let's see!
    let F' := Classical.choose h
    ¬ (X P)
  else
    False

theorem proj_inj (F : (Prop → Prop) → Prop) : proj (inj F) = F := by
  ext P
  dsimp [proj]
  have h_ex : ∃ (F' : (Prop → Prop) → Prop), inj F = inj F' := ⟨F, rfl⟩
  rw [dif_pos h_ex]
  -- We want to show: ¬ (inj F P) ↔ F P
  -- inj F P is: F P → False
  -- So ¬ (inj F P) is: (F P → False) → False
  dsimp [inj]
  constructor
  · intro h
    by_contra h_not
    exact h h_not
  · intro h h_not
    exact h_not h
