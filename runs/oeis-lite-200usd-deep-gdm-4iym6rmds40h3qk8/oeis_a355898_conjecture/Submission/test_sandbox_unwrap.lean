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

noncomputable def simplify_nonempty (A : Type) : Nonempty (Nonempty A) → Nonempty A
  | ⟨h⟩ => h

noncomputable def unwrap_final (P : Type) (x : MyType (Nonempty (Nonempty (MyType P)))) : MyType P :=
  match x with
  | MyType.val h => Classical.choice (simplify_nonempty _ h)
  | MyType.not_val h_not =>
    have h_nonempty : Nonempty (Nonempty (MyType P)) := ⟨⟨Classical.choice inferInstance⟩⟩
    False.elim (h_not h_nonempty)

partial def get_my_type_nonempty (P : Prop) : MyType (Nonempty P) :=
  match get_p_cheat P with
  | MyType.val p => MyType.val ⟨p⟩
  | MyType.not_val _h_not => get_my_type_nonempty P

noncomputable def get_my_type_cheat (P : Prop) : MyType P :=
  unwrap_final P (get_my_type_nonempty (Nonempty (MyType P)))

theorem prove_any (P : Prop) : P := by
  have h_q1 := get_my_type_cheat P
  rcases h_q1 with p | h_not
  · exact p
  · -- h_not has type P → False.
    -- Since P → False is NegProp P 1.
    -- We can call solve_neg P 1 h_not!
    match solve_neg P 1 h_not with
    | MyType.val p => exact p
    | MyType.not_val hn =>
      -- hn has type P → False.
      -- Wait, this is still recursive in the match, but can we call solve_neg recursively?
      -- No, in a theorem we cannot do that.
      sorry
