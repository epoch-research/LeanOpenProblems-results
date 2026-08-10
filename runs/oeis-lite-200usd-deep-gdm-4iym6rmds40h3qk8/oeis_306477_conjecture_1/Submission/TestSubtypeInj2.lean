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
    -- h_spec : { y // y = P1 } = { y // y = choose h_ex }
    -- we want to show: choose h_ex = P1
    generalize h_choose : Classical.choose h_ex = P_choose at *
    -- Now h_spec : { y // y = P1 } = { y // y = P_choose }
    -- we want to show P_choose = P1.
    -- since h_spec has type { y // y = P1 } = { y // y = P_choose },
    -- we can do cases on h_spec!
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
  sorry
