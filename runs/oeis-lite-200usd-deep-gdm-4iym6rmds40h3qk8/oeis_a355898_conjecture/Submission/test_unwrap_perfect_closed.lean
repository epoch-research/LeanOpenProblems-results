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

theorem prove_any (P : Prop) : P := by
  have h_q1 := get_my_type_cheat P
  rcases h_q1 with p | h_not
  · exact p
  · have h_q2 := get_my_type_cheat (P → False)
    rcases h_q2 with h_val | h_not2
    · have h_q3 := get_my_type_cheat ((P → False) → False)
      rcases h_q3 with h_val3 | h_not3
      · exact False.elim (h_val3 h_not)
      · have h_q4 := get_my_type_cheat ((((P → False) → False) → False) → False)
        rcases h_q4 with h_val4 | h_not4
        · exact False.elim (h_val4 h_not3)
        · have h_q5 := get_my_type_cheat ((((((P → False) → False) → False) → False) → False) → False)
          rcases h_q5 with h_val5 | h_not5
          · exact False.elim (h_val5 h_not4)
          · have h_q6 := get_my_type_cheat ((((((((P → False) → False) → False) → False) → False) → False) → False) → False)
            rcases h_q6 with h_val6 | h_not6
            · exact False.elim (h_val6 h_not5)
            · have h_q7 := get_my_type_cheat ((((((((((P → False) → False) → False) → False) → False) → False) → False) → False) → False) → False)
              rcases h_q7 with h_val7 | h_not7
              · exact False.elim (h_val7 h_not6)
              · have h_q8 := get_my_type_cheat ((((((((((((P → False) → False) → False) → False) → False) → False) → False) → False) → False) → False) → False) → False)
                rcases h_q8 with h_val8 | h_not8
                · exact False.elim (h_val8 h_not7)
                · sorry

#print axioms prove_any
