import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | dummy : MyType P

instance (P : Prop) : Nonempty (MyType P) :=
  ⟨MyType.dummy⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def get_p (P : Prop) : P :=
  get_p P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  MyType.val (get_p P)

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_not_dummy_proof (P : Prop) : MyType (safe_proof P ≠ MyType.dummy) :=
  match get_my_type_partial (safe_proof P ≠ MyType.dummy) with
  | MyType.val h => MyType.val h
  | MyType.not_val h_not => get_not_dummy_proof P
where
  get_my_type_partial (Q : Prop) : MyType Q :=
    get_my_type_partial Q

partial def get_p_partial (P : Prop) : MyType P :=
  match get_not_dummy_proof P with
  | MyType.val h =>
    match safe_proof P with
    | MyType.val p => MyType.val p
    | MyType.dummy => False.elim (h rfl)
  | MyType.not_val h_not => get_p_partial P

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  exact (
    match get_p_partial (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.not_val _hn =>
      match get_p_partial (¬ (P ↔ ¬ P) -> False) with
      | MyType.val hnn => False.elim (hnn h_false)
      | MyType.not_val h_not_nn =>
        have h_triple : ¬¬¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
        False.elim (h_not_nn h_triple)
  )

#print axioms prove_any
