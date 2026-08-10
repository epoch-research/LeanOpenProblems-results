open Classical

-- First, let's prove subtype_eq_inj
noncomputable def f {α : Type} (Y : Type) (default : α) : α :=
  if h : ∃ x : α, Y = { y : α // y = x } then
    Classical.choose h
  else
    default

theorem subtype_eq_inj {α : Type} (P1 P2 : α) (h : { y : α // y = P1 } = { y : α // y = P2 }) : P1 = P2 := by
  have h_prop : f { y : α // y = P1 } P1 = f { y : α // y = P2 } P1 := by
    rw [h]
  have h_P1 : f { y : α // y = P1 } P1 = P1 := by
    dsimp [f]
    have h_ex : ∃ P : α, { y : α // y = P1 } = { y : α // y = P } := ⟨P1, rfl⟩
    rw [dif_pos h_ex]
    have h_spec := Classical.choose_spec h_ex
    let val1 : { y // y = P1 } := ⟨P1, rfl⟩
    let val2 : { y // y = Classical.choose h_ex } := cast h_spec val1
    have h_eq : val2.val = Classical.choose h_ex := val2.property
    have h_heq : HEq val2 val1 := cast_heq h_spec val1
    have h_val_eq : val2.val = val1.val := eq_of_heq h_heq
    have h_val1 : val1.val = P1 := rfl
    rw [← h_eq, h_val_eq, h_val1]
  have h_P2 : f { y : α // y = P2 } P1 = P2 := by
    dsimp [f]
    have h_ex : ∃ P : α, { y : α // y = P2 } = { y : α // y = P } := ⟨P2, rfl⟩
    rw [dif_pos h_ex]
    have h_spec := Classical.choose_spec h_ex
    let val1 : { y // y = P2 } := ⟨P2, rfl⟩
    let val2 : { y // y = Classical.choose h_ex } := cast h_spec val1
    have h_eq : val2.val = Classical.choose h_ex := val2.property
    have h_heq : HEq val2 val1 := cast_heq h_spec val1
    have h_val_eq : val2.val = val1.val := eq_of_heq h_heq
    have h_val1 : val1.val = P2 := rfl
    rw [← h_eq, h_val_eq, h_val1]
  rw [h_P1, h_P2] at h_prop
  exact h_prop
