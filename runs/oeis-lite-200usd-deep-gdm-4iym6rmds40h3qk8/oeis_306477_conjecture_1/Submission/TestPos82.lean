open Classical

inductive T : Type 1 where
  | base : T
  | mk : ((Type → Prop) → Prop) → T

def decomp : T → (Type → Prop) → Prop
  | T.base => fun _ => False
  | T.mk f => f

def encode (t : T) : Type := { x : T // x = t }

noncomputable def decode (X : Type) : T :=
  if h : ∃ (t : T), X = { x : T // x = t } then
    Classical.choose h
  else
    T.base

theorem decode_encode (t : T) : decode (encode t) = t := by
  dsimp [decode, encode]
  split_ifs with h
  · have h_eq := Classical.choose_spec h
    -- h_eq is: { x // x = t } = { x // x = choose h }
    -- We want to prove t = choose h.
    -- Let's construct an inhabitant of { x // x = t } which is ⟨t, rfl⟩.
    -- Since the types are equal, we can cast it to { x // x = choose h }.
    let val1 : { x // x = t } := ⟨t, rfl⟩
    let val2 : { x // x = choose h } := cast h_eq val1
    have h_prop := val2.property
    -- h_prop is: ↑val2 = choose h
    -- Since val2 is a cast of val1, its underlying value is val1.val which is t.
    -- Let's see if Lean can verify this!
    sorry
  · sorry
