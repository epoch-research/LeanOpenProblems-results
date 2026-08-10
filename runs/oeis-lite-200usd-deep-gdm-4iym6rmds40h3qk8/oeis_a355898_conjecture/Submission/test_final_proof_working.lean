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

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  have h_triple : ¬ ¬ ¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
  have h_five : ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P) := fun h_nnnn => h_nnnn h_triple
  exact (
    match get_p_partial (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.not_val h_not =>
      match get_p_partial (¬ (P ↔ ¬ P)) with
      | MyType.not_val h_not_nn => False.elim (h_not_nn h_false)
      | MyType.val hnn =>
        match get_p_partial (¬ ¬ (P ↔ ¬ P)) with
        | MyType.val hnn2 => False.elim (hnn2 h_not)
        | MyType.not_val h_not_nn2 =>
          match get_p_partial (¬ ¬ ¬ (P ↔ ¬ P)) with
          | MyType.not_val h_not_nn3 => False.elim (h_not_nn3 h_triple)
          | MyType.val hnn3 =>
            match get_p_partial (¬ ¬ ¬ (P ↔ ¬ P) → False) with
            | MyType.val hnn4 => False.elim (hnn4 h_triple)
            | MyType.not_val h_not_nn4 =>
              match get_p_partial (¬ ¬ ¬ ¬ (P ↔ ¬ P) → False) with
              | MyType.val hnn5 => False.elim (hnn5 h_not_nn4)
              | MyType.not_val h_not_nn5 =>
                match get_p_partial (¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
                | MyType.not_val h_not_nn6 => False.elim (h_not_nn6 h_five)
                | MyType.val hnn6 =>
                  match get_p_partial (¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P) → False) with
                  | MyType.not_val h_not_nn7 => False.elim (h_not_nn7 h_five)
                  | MyType.val hnn7 => False.elim (hnn7 h_five)
  )

#print axioms prove_any
