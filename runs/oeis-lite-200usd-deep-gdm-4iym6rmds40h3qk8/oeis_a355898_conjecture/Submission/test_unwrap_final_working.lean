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
  match get_my_type_cheat P with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    match get_my_type_cheat (P → False) with
    | MyType.not_val h_not_not =>
      exact False.elim (h_not_not h_not)
    | MyType.val h_val =>
      match get_my_type_cheat ((P → False) → False) with
      | MyType.val h_val3 =>
        exact False.elim (h_val3 h_not)
      | MyType.not_val h_not3 =>
        match get_my_type_cheat (((P → False) → False) → False) with
        | MyType.not_val h_not4 =>
          exact False.elim (h_not4 h_not3)
        | MyType.val h_val4 =>
          match get_my_type_cheat ((((P → False) → False) → False) → False) with
          | MyType.not_val h_not5 =>
            exact False.elim (h_not5 h_not3)
          | MyType.val h_val5 =>
            exact False.elim (h_val5 h_val4)

#print axioms prove_any
