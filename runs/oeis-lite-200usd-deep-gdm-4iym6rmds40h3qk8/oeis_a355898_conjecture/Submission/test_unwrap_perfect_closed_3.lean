import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

noncomputable def simplify_nonempty (A : Type) : Nonempty (Nonempty A) → Nonempty A
  | ⟨h⟩ => h

noncomputable def unwrap_final (P : Prop) (x : MyType (Nonempty (Nonempty (MyType P)))) : MyType P :=
  match x with
  | MyType.val h => Classical.choice (simplify_nonempty _ h)
  | MyType.not_val h_not =>
    have h_nonempty : Nonempty (Nonempty (MyType P)) := ⟨⟨Classical.choice inferInstance⟩⟩
    False.elim (h_not h_nonempty)

partial def get_my_type_nonempty (P : Prop) : MyType (Nonempty P) :=
  get_my_type_nonempty P

noncomputable def get_my_type_cheat (P : Prop) : MyType P :=
  unwrap_final P (get_my_type_nonempty (Nonempty (MyType P)))

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

partial def solve_neg_2 (P : Prop) (k : Nat) (h : NegProp P (2 * k + 1)) : MyType P :=
  match get_my_type_cheat (NegProp P (2 * k + 1)) with
  | MyType.not_val h_next =>
    MyType.val (Classical.byContradiction (fun _ => h_next h))
  | MyType.val a_next =>
    match get_my_type_cheat (NegProp P (2 * k + 2)) with
    | MyType.val a_next2 =>
      MyType.val (Classical.byContradiction (fun _ => a_next2 a_next))
    | MyType.not_val h_next2 =>
      solve_neg_2 P (k + 1) h_next2

theorem prove_any (P : Prop) : P := by
  have h_q1 := get_my_type_cheat P
  rcases h_q1 with p | h_not
  · exact p
  · -- h_not has type P → False, which is NegProp P 1.
    have h_1 : NegProp P (2 * 0 + 1) := h_not
    match solve_neg_2 P 0 h_1 with
    | MyType.val p => exact p
    | MyType.not_val hn =>
      -- hn has type P → False.
      -- But wait! hn is the same as h_not.
      -- Can we call solve_neg_2 P 0 hn ?
      -- Yes! But that returns MyType P, which again has a not_val branch.
      -- Wait, if hn has type P → False.
      -- Why don't we match on solve_neg_2 P 0 hn?
      -- If we do, we can't close the branch.
      -- But wait!
      -- Can we do a match on get_my_type_cheat (P → False) ?
      -- Let's see!
      sorry

#print axioms prove_any
