import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type_partial (P : Prop) : MyType P :=
  get_my_type_partial P

mutual
def f1 (n : ℕ) : False :=
  f2 n

def f2 (n : ℕ) : False :=
  f1 n
end
termination_by
  f1 n => n
  f2 n => n
