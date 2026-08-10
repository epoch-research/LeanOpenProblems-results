open Classical

noncomputable def get_val {α : Type} (Y : Type) (y : Y) (h : ∃ f : α → Prop, Y = Subtype f) : α :=
  let f' := Classical.choose h
  have h_eq : Y = Subtype f' := Classical.choose_spec h
  Subtype.val (cast h_eq y)

theorem get_val_spec {α : Type} (f : α → Prop) (y : Subtype f) :
    get_val (Subtype f) y ⟨f, rfl⟩ = y.val := by
  dsimp [get_val]
  generalize h_ex : ⟨f, rfl⟩ = h
  -- Now we want to prove that the result does not depend on the proof `h`.
  -- Since `h` is in `Prop`, any two proofs of `∃ f', Subtype f = Subtype f'` are equal!
  -- So we can just rewrite `h` to any other proof!
  sorry
