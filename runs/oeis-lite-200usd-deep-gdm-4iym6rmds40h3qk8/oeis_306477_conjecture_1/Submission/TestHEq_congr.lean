open Classical

noncomputable def f_val {α : Type} (Y : Type) (y : Y) (default : α) : α :=
  if h : ∃ P : α, Y = { y : α // y = P } then
    let P := Classical.choose h
    have h_eq : Y = { y : α // y = P } := Classical.choose_spec h
    match cast h_eq y with
    | ⟨val, _⟩ => val
  else
    default

theorem f_val_eq {α : Type} (P : α) (y : { y : α // y = P }) (default : α) :
    f_val { y : α // y = P } y default = y.val := by
  dsimp [f_val]
  have h_ex : ∃ P' : α, { y : α // y = P } = { y : α // y = P' } := ⟨P, rfl⟩
  rw [dif_pos h_ex]
  generalize h_choose : Classical.choose h_ex = P_choose at *
  have h_spec : { y // y = P } = { y // y = P_choose } := Classical.choose_spec h_ex
  -- Now we want to prove (match cast h_spec y with | ⟨val, _⟩ => val) = y.val
  -- We can use a lemma!
  sorry
