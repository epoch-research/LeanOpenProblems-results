open Classical

def encode (f : Prop → Prop) : Type := { p : Prop // f p }

noncomputable def my_val (Y : Type) (y : Y) : Prop :=
  if h : ∃ (f : Prop → Prop), Y = encode f then
    let f := Classical.choose h
    let h_eq := Classical.choose_spec h
    let y' : encode f := cast h_eq y
    y'.val
  else
    False

theorem my_val_encode (f : Prop → Prop) (y : encode f) : my_val (encode f) y = y.val := by
  dsimp [my_val]
  have h_ex : ∃ (f' : Prop → Prop), encode f = encode f' := ⟨f, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  generalize h_choose : Classical.choose h_ex = f' at *
  generalize h_spec = eq_proof
  cases eq_proof
  rfl
