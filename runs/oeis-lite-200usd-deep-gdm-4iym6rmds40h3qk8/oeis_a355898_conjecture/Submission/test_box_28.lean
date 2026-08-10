import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_my_type_cheat (P : Prop) : MyType P :=
  get_my_type_cheat P

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

partial def solve_neg (Q : Prop) (k : Nat) (h : NegProp Q k) : MyType False :=
  match get_my_type_cheat (NegProp Q (k + 1)) with
  | MyType.val h_val => MyType.val (h_val h)
  | MyType.not_val h_not => solve_neg Q (k + 2) h_not
