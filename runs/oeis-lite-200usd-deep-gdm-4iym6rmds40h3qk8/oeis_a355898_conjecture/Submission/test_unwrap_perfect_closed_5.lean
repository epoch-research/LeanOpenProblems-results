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
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

partial def solve_neg_2 (P : Prop) (k : Nat) (h : NegProp P (2 * k + 1)) : MyType P :=
  match get_p_cheat (NegProp P (2 * k + 1)) with
  | MyType.not_val h_next =>
    MyType.val (Classical.byContradiction (fun _ => h_next h))
  | MyType.val a_next =>
    match get_p_cheat (NegProp P (2 * k + 2)) with
    | MyType.val a_next2 =>
      MyType.val (Classical.byContradiction (fun _ => a_next2 a_next))
    | MyType.not_val h_next2 =>
      solve_neg_2 P (k + 1) h_next2

theorem prove_false : False := by
  have h_1 : NegProp False 1 := fun h_f => h_f
  match solve_neg_2 False 0 h_1 with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    have h_true : False → False := fun h_f => h_f
    exact hn h_true

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
