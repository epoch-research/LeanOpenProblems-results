import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

noncomputable def unwrap (P : Prop) (x : MyType (MyType P)) : MyType P :=
  match x with
  | MyType.val (MyType.val p) => MyType.val p
  | MyType.val (MyType.not_val hn) => MyType.not_val hn
  | MyType.not_val h_not_mytype => False.elim (h_not_mytype (Classical.choice inferInstance))

#print axioms unwrap
