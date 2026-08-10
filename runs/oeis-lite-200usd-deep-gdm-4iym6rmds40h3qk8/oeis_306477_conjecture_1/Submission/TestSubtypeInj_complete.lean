open Classical

noncomputable def get_prop {α : Type} (Y : Type) (default : α) : α :=
  if h : ∃ P : α, Y = { y : α // y = P } then
    Classical.choose h
  else
    default

theorem subtype_eq_inj {α : Type} (P1 P2 : α) (h : { y : α // y = P1 } = { y : α // y = P2 }) : P1 = P2 := by
  have h_prop : get_prop { y : α // y = P1 } P1 = get_prop { y : α // y = P2 } P1 := by
    rw [h]
  have h_P1 : get_prop { y : α // y = P1 } P1 = P1 := by
    dsimp [get_prop]
    have h_ex : ∃ P : α, { y : α // y = P1 } = { y : α // y = P } := ⟨P1, rfl⟩
    rw [dif_pos h_ex]
    have h_spec := Classical.choose_spec h_ex
    generalize h_choose : Classical.choose h_ex = P_choose at *
    cases h_spec
    rfl
  have h_P2 : get_prop { y : α // y = P2 } P1 = P2 := by
    dsimp [get_prop]
    have h_ex : ∃ P : α, { y : α // y = P2 } = { y : α // y = P } := ⟨P2, rfl⟩
    rw [dif_pos h_ex]
    have h_spec := Classical.choose_spec h_ex
    generalize h_choose : Classical.choose h_ex = P_choose at *
    cases h_spec
    rfl
  rw [h_P1, h_P2] at h_prop
  exact h_prop
