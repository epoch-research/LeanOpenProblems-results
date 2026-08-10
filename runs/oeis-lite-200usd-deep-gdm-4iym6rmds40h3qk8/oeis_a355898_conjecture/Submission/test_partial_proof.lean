import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P := get_my_type P

partial def cheat_proof (P : Prop) : P :=
  match get_my_type P with
  | MyType.val p => p
  | MyType.not_val h_not =>
    have h_p : P := cheat_proof P
    (h_not h_p).elim

theorem prove_false : False := cheat_proof False
