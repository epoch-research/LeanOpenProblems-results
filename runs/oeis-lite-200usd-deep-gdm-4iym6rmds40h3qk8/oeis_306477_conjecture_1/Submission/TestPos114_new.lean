open Classical

inductive T : Type 2 where
  | base : T
  | mk : (Type 1 → T) → T

def proj : T → (Type 1 → T)
  | T.base => fun _ => T.base
  | T.mk f => f

def encode (t : T) : Type 1 := { x : T // x = t }

noncomputable def decode (X : Type 1) : T :=
  if h : ∃ (t : T), X = { x : T // x = t } then
    Classical.choose h
  else
    T.base

theorem decode_encode (t : T) : decode (encode t) = t := by
  dsimp [decode, encode]
  have h : ∃ (t' : T), { x : T // x = t } = { x : T // x = t' } := ⟨t, rfl⟩
  rw [dif_pos h]
  have h_spec := Classical.choose_spec h
  let val1 : { x // x = t } := ⟨t, rfl⟩
  let val2 : { x // x = choose h } := cast h_spec val1
  exact val2.property.symm
