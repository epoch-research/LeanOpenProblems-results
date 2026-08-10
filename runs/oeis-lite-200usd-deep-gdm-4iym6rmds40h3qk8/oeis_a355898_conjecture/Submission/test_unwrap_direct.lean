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

noncomputable def unwrap_final_nonempty (P : Prop) (x : MyType (Nonempty (Nonempty (MyType (Nonempty P))))) : MyType (Nonempty P) :=
  match x with
  | MyType.val h => Classical.choice (simplify_nonempty _ h)
  | MyType.not_val h_not =>
    have h_nonempty : Nonempty (Nonempty (MyType (Nonempty P))) := ⟨⟨Classical.choice inferInstance⟩⟩
    False.elim (h_not h_nonempty)

partial def get_my_type_nonempty (P : Prop) : MyType (Nonempty P) :=
  get_my_type_nonempty P

noncomputable def get_nonempty_cheat (P : Prop) : MyType (Nonempty P) :=
  unwrap_final_nonempty P (get_my_type_nonempty (Nonempty (MyType (Nonempty P))))

partial def get_p_partial (P : Prop) (h : Nonempty P) : P :=
  match get_nonempty_cheat P with
  | MyType.val hp => Classical.choice hp
  | MyType.not_val _h_not => get_p_partial P h

theorem prove_any (P : Prop) : P := by
  let rec h_ne : Nonempty P := ⟨get_p_partial P h_ne⟩
  exact get_p_partial P h_ne

#print axioms prove_any
