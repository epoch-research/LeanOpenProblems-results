open Classical

def encode (f : Prop → Prop) : Type := { p : Prop // f p }

noncomputable def my_val (Y : Type) (y : Y) : Prop :=
  if h : ∃ (f : Prop → Prop), Y = encode f then
    let f := Classical.choose h
    let h_eq := Classical.choose_spec h
    let y' : encode f := cast h_eq.symm y
    y'.val
  else
    False

theorem my_val_encode (f : Prop → Prop) (y : encode f) : my_val (encode f) y = y.val := by
  dsimp [my_val]
  have h_ex : ∃ (f' : Prop → Prop), encode f = encode f' := ⟨f, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec : encode f = encode (choose h_ex)
  -- we want to show: (cast h_spec.symm y).val = y.val
  -- Let's generalize choose h_ex to f'
  generalize h_choose : Classical.choose h_ex = f' at *
  -- Now h_spec : encode f = encode f'
  -- y' : encode f' := cast h_spec.symm y
  -- we want to show y'.val = y.val
  -- since h_spec : encode f = encode f', we can do cases on h_spec!
  generalize h_spec = eq_proof
  cases eq_proof
  rfl
