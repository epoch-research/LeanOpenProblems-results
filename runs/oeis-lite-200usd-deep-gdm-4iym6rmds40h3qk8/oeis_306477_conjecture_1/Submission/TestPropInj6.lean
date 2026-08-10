open Classical

noncomputable def get_val_generic (Y : Type) (y : Y) : Prop :=
  if h : ∃ P : Prop, Y = { x : Prop // x = P } then
    let P := Classical.choose h
    have h_eq : Y = { x : Prop // x = P } := Classical.choose_spec h
    (cast h_eq y).val
  else
    False

def F {α : Type} (f : α → Prop) (Y : Type) (eq : Y = Subtype f) (y : Y) : α :=
  match cast eq y with
  | ⟨val, _⟩ => val

theorem cast_val_lemma {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (y : Subtype f) :
    F f Y eq.symm (cast eq y) = y.val := by
  cases eq
  rfl

theorem cast_symm_cast {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (x : Subtype f) :
    cast eq.symm (cast eq x) = x := by
  cases eq
  rfl

theorem get_val_generic_spec (P : Prop) (y : { x : Prop // x = P }) :
    get_val_generic { x : Prop // x = P } y = P := by
  dsimp [get_val_generic]
  have h_ex : ∃ P' : Prop, { x : Prop // x = P } = { x : Prop // x = P' } := ⟨P, rfl⟩
  rw [dif_pos h_ex]
  generalize h_choose : Classical.choose h_ex = P_choose at *
  have h_spec : { x // x = P } = { x // x = P_choose } := Classical.choose_spec h_ex
  -- LHS is (cast h_spec y).val.
  -- By definition of F: F (fun x => x = P_choose) { x // x = P } h_spec.symm y
  --   = (cast h_spec y).val.
  -- Wait, let's show that (cast h_spec y).val = P.
  -- Since cast h_spec y has type { x // x = P_choose }.
  -- Its .val is equal to P_choose (by .property).
  -- So we want to show P_choose = P.
  -- Since h_spec : { x // x = P } = { x // x = P_choose }.
  -- Can we prove P = P_choose?
  sorry
