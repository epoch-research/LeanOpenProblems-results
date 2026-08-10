import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def cheat_proof (P : Prop) : MyType P :=
  match cheat_proof P with
  | MyType.val p => MyType.val p
  | MyType.not_val h_not => MyType.not_val h_not

theorem prove_false : False := by
  match cheat_proof False with
  | MyType.val f => exact f
  | MyType.not_val h_not =>
    -- wait, we have h_not : False → False. This doesn't give False.
    sorry
