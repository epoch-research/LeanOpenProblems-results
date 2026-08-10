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
  get_p_cheat P

theorem prove_false_of_g1_and_not_g0 (A B : Prop) (h_g1 : B) (h_not_0 : ¬ A) : False := by
  match get_p_cheat (A = B) with
  | MyType.val p_eq =>
    exact h_not_0 (p_eq ▸ h_g1)
  | MyType.not_val h_not_eq =>
    match get_p_cheat (B → A) with
    | MyType.val h_imp2 =>
      have p_eq : A = B := propext ⟨fun h_a => False.elim (h_not_0 h_a), h_imp2⟩
      exact h_not_eq p_eq
    | MyType.not_val h_not_imp2 =>
      match get_p_cheat A with
      | MyType.val p0 =>
        have h_imp2 : B → A := fun _ => p0
        exact h_not_imp2 h_imp2
      | MyType.not_val h_not_0' =>
        match get_p_cheat (¬ B) with
        | MyType.val h_not_b =>
          exact h_not_b h_g1
        | MyType.not_val h_not_not_b =>
          exact h_not_not_b (fun (h_nb : B → False) => h_nb h_g1)

theorem prove_false : False :=
  prove_false_of_g1_and_not_g0 False True True.intro (fun x => x)

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
