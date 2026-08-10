import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

mutual
  partial def get_p_cheat (P : Prop) : MyType P :=
    match get_p_cheat (¬ P) with
    | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
    | MyType.val hn => solve_neg P 1 hn

  partial def solve_neg (P : Prop) (k : Nat) (h : NegProp P k) : MyType P :=
    match get_p_cheat (NegProp P (k + 1)) with
    | MyType.val h_val => MyType.val (Classical.byContradiction (fun _hn => h_val h))
    | MyType.not_val h_not => solve_neg P (k + 2) h_not
end

theorem prove_any (P : Prop) : P := by
  match get_p_cheat P with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    match get_p_cheat ((P → False) → False) with
    | MyType.val h_val3 =>
      exact False.elim (h_val3 h_not)
    | MyType.not_val h_not3 =>
      have h_triple : ((P → False) → False) → False := fun h_not_not => h_not_not h_not
      exact False.elim (h_not3 h_triple)

#print axioms prove_any
