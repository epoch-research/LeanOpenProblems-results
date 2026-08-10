import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

noncomputable def unwrap (P : Prop) (x : MyType (Nonempty (MyType P))) : MyType P :=
  match x with
  | MyType.val h => Classical.choice h
  | MyType.not_val h_not => False.elim (h_not ⟨Classical.choice inferInstance⟩)

#print axioms unwrap
