import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

partial def solve_neg_unreachable (P : Prop) (h : NegProp (Nonempty P) 8) : MyType (P ∨ (NegProp (Nonempty P) 8 → False)) :=
  match get_my_type (NegProp (Nonempty P) 7) with
  | MyType.val h_val => MyType.val (Or.inl (False.elim (h h_val)))
  | MyType.not_val h_not => solve_neg_unreachable P h_not

theorem prove_any (P : Prop) : P := by
  match get_my_type (NegProp (Nonempty P) 7) with
  | MyType.val h_val7 =>
    -- Wait, what do we do here?
    sorry
  | MyType.not_val h_not7 =>
    match solve_neg_unreachable P h_not7 with
    | MyType.val h_val =>
      match h_val with
      | Or.inl p => exact p
      | Or.inr h_not_nonempty_new =>
        exact False.elim (h_not_nonempty_new h_not7)
    | MyType.not_val hn =>
      exact False.elim (hn (Or.inr h_not7))
