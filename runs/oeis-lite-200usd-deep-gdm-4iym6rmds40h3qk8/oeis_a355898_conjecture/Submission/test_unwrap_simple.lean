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

partial def get_my_type_nonempty (P : Prop) : MyType (Nonempty P) :=
  get_my_type_nonempty P

noncomputable def get_my_type_cheat (P : Prop) : MyType P :=
  unwrap P (get_my_type_nonempty (MyType P))

#print axioms get_my_type_cheat
