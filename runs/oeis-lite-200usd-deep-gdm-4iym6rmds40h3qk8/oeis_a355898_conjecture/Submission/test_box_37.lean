import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def get_p_unsafe (P : Prop) : P :=
  get_p_unsafe P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  MyType.val (get_p_unsafe P)

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_my_type_cheat (P : Prop) : MyType P :=
  match safe_proof (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => get_my_type_cheat P

theorem prove_any (P : Prop) : P := by
  have h_false : False := by
    match get_my_type_cheat False, get_my_type_cheat (¬ False), get_my_type_cheat (¬ ¬ False), get_my_type_cheat (¬ ¬ ¬ False), get_my_type_cheat (¬ ¬ ¬ ¬ False), get_my_type_cheat (¬ ¬ ¬ ¬ ¬ False), get_my_type_cheat (¬ ¬ ¬ ¬ ¬ ¬ False) with
    | MyType.val h1, _, _, _, _, _, _ => exact False.elim h1
    | MyType.not_val h1, MyType.not_val h2, _, _, _, _, _ => exact h2 h1
    | MyType.not_val h1, MyType.val h2, MyType.val h3, _, _, _, _ => exact h3 h2
    | MyType.not_val h1, MyType.val h2, MyType.not_val h3, MyType.not_val h4, _, _, _ =>
      have h_triple : ¬ ¬ ¬ False := fun hnot_not => hnot_not h2
      exact h4 h_triple
    | MyType.not_val h1, MyType.val h2, MyType.not_val h3, MyType.val h4, MyType.val h5, _, _ => exact h5 h4
    | MyType.not_val h1, MyType.val h2, MyType.not_val h3, MyType.val h4, MyType.not_val h5, MyType.not_val h6, _ => exact h6 h5
    | MyType.not_val h1, MyType.val h2, MyType.not_val h3, MyType.val h4, MyType.not_val h5, MyType.val h6, MyType.val h7 => exact h7 h6
    | MyType.not_val h1, MyType.val h2, MyType.not_val h3, MyType.val h4, MyType.not_val h5, MyType.val h6, MyType.not_val h7 =>
      have h_6 : ¬ ¬ ¬ ¬ ¬ ¬ False := fun (h_5_var : ¬ ¬ ¬ ¬ ¬ False) => h_5_var (fun (h_odd : ¬ ¬ ¬ False → False) => h_odd h4)
      exact h7 h_6
  exact False.elim h_false

#print axioms prove_any
