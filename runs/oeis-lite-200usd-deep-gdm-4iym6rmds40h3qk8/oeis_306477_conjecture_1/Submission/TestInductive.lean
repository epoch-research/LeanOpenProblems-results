open Classical

inductive inj (F : (Prop → Prop) → Prop) : Type where
  | mk : (Σ (P : Prop → Prop), PLift (F P)) → inj F

def dest {F : (Prop → Prop) → Prop} (x : inj F) : Σ (P : Prop → Prop), PLift (F P)
  | inj.mk y => y

noncomputable def proj (X : Type) (P : Prop → Prop) : Prop :=
  if h : ∃ (F : (Prop → Prop) → Prop), X = inj F then
    let h_eq := Classical.choose_spec h
    -- cast h_eq to inj (choose h)
    ∃ (x : X), (dest (cast h_eq x)).fst = P
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
  -- Now choose h_ex is replaced by F!
  constructor
  · intro h
    cases h with
    | intro x h_eq =>
      -- x : inj F
      -- h_eq : (dest x).fst = P
      have h_x : x = inj.mk (dest x) := by
        cases x
        rfl
      let y := dest x
      cases y with
      | mk P' val =>
        dsimp at h_eq
        rw [← h_eq]
        exact val.down
  · intro h
    let x : inj F := inj.mk ⟨P, ⟨h⟩⟩
    exact ⟨x, rfl⟩
