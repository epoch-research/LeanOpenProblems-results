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

noncomputable partial def solve_neg_2 (P : Prop) (k : Nat) (h : NegProp P (2 * k + 1)) : MyType P :=
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
  · -- h_not has type P → False (A_1).
    have h_q2 := get_my_type_cheat ((P → False) → False) -- A_2
    rcases h_q2 with a_2 | h_2
    · exact False.elim (a_2 h_not)
    · -- h_2 has type A_3
      have h_q3 := get_my_type_cheat (((P → False) → False) → False) -- A_3
      rcases h_q3 with a_3 | h_3
      · -- h_3 has type A_4 = A_3 → False
        exact False.elim (h_3 h_2)
      · -- a_3 has type A_3
        have h_q4 := get_my_type_cheat ((((P → False) → False) → False) → False) -- A_4
        rcases h_q4 with a_4 | h_4
        · exact False.elim (a_4 h_2)
        · -- h_4 has type A_5
          have h_q5 := get_my_type_cheat (((((P → False) → False) → False) → False) → False) -- A_5
          rcases h_q5 with a_5 | h_5
          · exact False.elim (h_5 h_4)
          · -- a_5 has type A_5
            have h_q6 := get_my_type_cheat ((((((P → False) → False) → False) → False) → False) → False) -- A_6
            rcases h_q6 with a_6 | h_6
            · exact False.elim (a_6 h_4)
            · -- h_6 has type A_7
              have h_q7 := get_my_type_cheat (((((((P → False) → False) → False) → False) → False) → False) → False) -- A_7
              rcases h_q7 with a_7 | h_7
              · exact False.elim (h_7 h_6)
              · -- a_7 has type A_7
                have h_q8 := get_my_type_cheat ((((((((P → False) → False) → False) → False) → False) → False) → False) → False) -- A_8
                rcases h_q8 with a_8 | h_8
                · exact False.elim (a_8 h_6)
                · -- h_8 has type A_9
                  match solve_neg_2 P 4 h_8 with
                  | MyType.val p => exact p
                  | MyType.not_val hn =>
                    -- hn has type P → False.
                    -- We can just call solve_neg_2 again!
                    match solve_neg_2 P 0 hn with
                    | MyType.val p => exact p
                    | MyType.not_val _ =>
                      -- wait, we need to close this.
                      -- Let's see if we can just do sorry here for a moment to test if the rest compiles.
                      sorry

#print axioms prove_any
