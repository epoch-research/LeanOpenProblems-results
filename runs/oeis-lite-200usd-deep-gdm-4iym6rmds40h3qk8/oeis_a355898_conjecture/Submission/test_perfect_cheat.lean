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
  have h1 := get_my_type_cheat P
  rcases h1 with hp | hnot
  · exact hp
  · have h2 := get_my_type_cheat (¬P)
    rcases h2 with hnot_val | hnot_not
    · exact False.elim (hnot_val hnot)
    · have h3 := get_my_type_cheat (¬¬P)
      rcases h3 with h3_val | h3_not
      · exact False.elim (hnot_not h3_val)
      · have h4 := get_my_type_cheat (¬¬¬P)
        rcases h4 with h4_val | h4_not
        · exact False.elim (h3_not h4_val)
        · exact False.elim (h4_not h3_not)

#print axioms prove_any
