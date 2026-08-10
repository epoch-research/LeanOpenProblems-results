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

partial def get_is_val_proof (P : Prop) : MyType (is_val (safe_proof P)) :=
  match safe_proof (is_val (safe_proof P)) with
  | MyType.val h => MyType.val h
  | MyType.not_val _h_not => get_is_val_proof P

partial def get_p_partial (P : Prop) : MyType P :=
  match get_is_val_proof P with
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
  exact (
    match get_p_partial (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.not_val _h_not =>
      match get_p_partial (¬ ¬ (P ↔ ¬ P)) with
      | MyType.val hnn => False.elim (hnn h_false)
      | MyType.not_val h_not_nn =>
        match get_p_partial (¬ ¬ ¬ (P ↔ ¬ P)) with
        | MyType.not_val h_not_nn2 => False.elim (h_not_nn2 h_triple)
        | MyType.val hnn2 =>
          match get_p_partial (¬ ¬ ¬ (P ↔ ¬ P) → False) with
          | MyType.val hnn3 => False.elim (hnn3 h_triple)
          | MyType.not_val h_not_nn3 =>
            match get_p_partial (¬ ¬ ¬ ¬ (P ↔ ¬ P) → False) with
            | MyType.val hnn4 => False.elim (hnn4 h_not_nn3)
            | MyType.not_val h_not_nn4 =>
              match get_p_partial (¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P) → False) with
              | MyType.val hnn5 => False.elim (h_not_nn4 hnn5)
              | MyType.not_val h_not_nn5 => False.elim (h_not_nn5 h_not_nn4)
  )

#print axioms prove_any
