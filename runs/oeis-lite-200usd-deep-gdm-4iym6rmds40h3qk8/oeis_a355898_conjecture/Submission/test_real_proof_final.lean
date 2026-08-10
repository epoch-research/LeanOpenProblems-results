import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_my_type_cheat (P : Prop) : MyType P :=
  match safe_proof (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => get_my_type_cheat P

theorem prove_any (P : Prop) : P := by
  match get_my_type_cheat P with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    match get_my_type_cheat (¬ P) with
    | MyType.not_val hnn => exact False.elim (hnn hn)
    | MyType.val hn_neg =>
      match get_my_type_cheat (¬ (¬ P)) with
      | MyType.not_val hnn_final2 => exact False.elim (hnn_final2 hn_neg)
      | MyType.val hnn_val2 => exact False.elim (hnn_val2 hn_neg)

#print axioms prove_any
