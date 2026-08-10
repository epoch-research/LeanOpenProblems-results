open Classical

noncomputable def get_val_from_subtype {α : Type} (Y : Type) (y : Y) (h : ∃ P : α, Y = { y : α // y = P }) : α :=
  let P_choose := Classical.choose h
  have h_eq : Y = { y : α // y = P_choose } := Classical.choose_spec h
  match cast h_eq y with
  | ⟨val, _⟩ => val

theorem get_val_from_subtype_eq {α : Type} (P : α) (y : { y : α // y = P }) (h : ∃ P' : α, { y : α // y = P } = { y : α // y = P' }) :
    get_val_from_subtype { y : α // y = P } y h = P := by
  dsimp [get_val_from_subtype]
  generalize h_choose : Classical.choose h = P_choose at *
  have h_spec : { y // y = P } = { y // y = P_choose } := Classical.choose_spec h
  -- Now we have h_spec : { y // y = P } = { y // y = P_choose }
  -- we want to show: (match cast h_spec y with | ⟨val, _⟩ => val) = P
  -- Since we have h_spec, we can use cast_symm_cast!
  sorry
