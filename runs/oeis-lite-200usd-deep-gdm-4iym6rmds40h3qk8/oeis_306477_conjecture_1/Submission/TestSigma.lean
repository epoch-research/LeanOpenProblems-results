open Classical

def inj (F : (Type → Prop) → Prop) : Type :=
  Sigma (fun (P : Type → Prop) => PLift (F P))

def proj (X : Type) (P : Type → Prop) : Prop :=
  Exists (fun (x : X) => x.1 = P)

theorem proj_inj (F : (Type → Prop) → Prop) : proj (inj F) = F := by
  ext P
  apply propext
  constructor
  · intro h
    rcases h with ⟨x, h_eq⟩
    -- x is in inj F, so x is of the form ⟨P', val⟩
    rcases x with ⟨P', ⟨h_FP'⟩⟩
    -- h_eq is P' = P
    dsimp at h_eq
    rw [← h_eq]
    exact h_FP'
  · intro h
    let x : inj F := ⟨P, ⟨h⟩⟩
    exact ⟨x, rfl⟩
