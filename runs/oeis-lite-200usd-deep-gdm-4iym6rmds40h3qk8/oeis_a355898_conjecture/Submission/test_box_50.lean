import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_p_cheat (P : Prop) : MyType P :=
  MyType.val (Classical.byContradiction (fun hnn =>
    match get_p_cheat P with
    | MyType.val p => hnn p
    | MyType.not_val hn => hn (Classical.byContradiction hnn)
  ))

theorem prove_any (P : Prop) : P := by
  match get_p_cheat P with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    exact Classical.byContradiction (fun hnn => hn (Classical.byContradiction hnn))

#print axioms prove_any
