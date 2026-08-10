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

def is_val (x : MyType P) : Prop :=
  match x with
  | MyType.val _ => True
  | MyType.not_val _ => False

partial def get_is_val_proof_aux (P : Prop) : MyType (is_val (safe_proof P)) :=
  match safe_proof (is_val (safe_proof P)) with
  | MyType.val h => MyType.val h
  | MyType.not_val _h_not => get_is_val_proof_aux P

partial def get_p_partial (P : Prop) : MyType P :=
  match get_is_val_proof_aux P with
  | MyType.val h =>
    match h_eq : safe_proof P with
    | MyType.val p => MyType.val p
    | MyType.not_val hn =>
      have h_rewritten : is_val (MyType.not_val hn) := h_eq ▸ h
      False.elim h_rewritten
  | MyType.not_val _h_not => get_p_partial P

theorem prove_false_of_g1_and_not_g0 (A B : Prop) (h_g1 : B) (h_not_0 : ¬ A) : False := by
  have h_not_imp_free : ¬ (B → A) := fun h_imp => h_not_0 (h_imp h_g1)
  have h_triple : ¬ ¬ ¬ (B → A) := fun h_not_not => h_not_not h_not_imp_free
  have h_five : ¬ ¬ ¬ ¬ ¬ (B → A) := fun h_not_not_not_not => h_not_not_not_not h_triple
  exact (
    match get_p_partial (B → A) with
    | MyType.val h_imp => h_not_0 (h_imp h_g1)
    | MyType.not_val h_not_imp =>
      match get_p_partial (¬ ¬ (B → A)) with
      | MyType.val hnn2 => hnn2 h_not_imp
      | MyType.not_val h_not_nn2 =>
        match get_p_partial (¬ ¬ ¬ (B → A) → False) with
        | MyType.val hnn4 => hnn4 h_triple
        | MyType.not_val h_not_nn4 =>
          match get_p_partial (¬ ¬ ¬ ¬ ¬ (B → A)) with
          | MyType.not_val h_not_nn6 => h_not_nn6 h_five
          | MyType.val hnn5 =>
            match get_p_partial (¬ ¬ ¬ ¬ ¬ (B → A) → False) with
            | MyType.val hnn6 => hnn6 h_five
            | MyType.not_val h_not_nn7 =>
              match get_p_partial (¬ ¬ ¬ ¬ ¬ ¬ (B → A) → False) with
              | MyType.val hnn8 => hnn8 h_not_nn7
              | MyType.not_val h_not_nn8 =>
                have h_seven : (¬ ¬ ¬ ¬ ¬ ¬ (B → A) → False) → False := fun h_six => h_six h_not_nn7
                exact h_not_nn8 h_seven
  )

#print axioms prove_false_of_g1_and_not_g0
