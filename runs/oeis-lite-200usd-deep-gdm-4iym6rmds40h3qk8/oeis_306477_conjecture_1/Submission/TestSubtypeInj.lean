open Classical

noncomputable def f {α : Type} [Inhabited α] (Y : Type) : α :=
  if h : Nonempty Y then
    (Classical.choice h).val
  else
    default

theorem subtype_eq_inj {α : Type} [Inhabited α] (P1 P2 : α) (h : { y : α // y = P1 } = { y : α // y = P2 }) : P1 = P2 := by
  have h_eq : f { y : α // y = P1 } = f { y : α // y = P2 } := by
    rw [h]
  have h_P1 : f { y : α // y = P1 } = P1 := by
    dsimp [f]
    have h_ne : Nonempty { y : α // y = P1 } := ⟨⟨P1, rfl⟩⟩
    rw [dif_pos h_ne]
    exact (Classical.choice h_ne).property
  have h_P2 : f { y : α // y = P2 } = P2 := by
    dsimp [f]
    have h_ne : Nonempty { y : α // y = P2 } := ⟨⟨P2, rfl⟩⟩
    rw [dif_pos h_ne]
    exact (Classical.choice h_ne).property
  rw [h_P1, h_P2] at h_eq
  exact h_eq
