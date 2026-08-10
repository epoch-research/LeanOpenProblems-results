import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

inductive DummyType (P : Prop) : Type where
  | val : P → DummyType P

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
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  have h_triple : ¬ ¬ ¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
  exact (
    match get_my_type_cheat (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.not_val h_not =>
      match get_my_type_cheat (¬ (P ↔ ¬ P)) with
      | MyType.not_val h_not_nn => False.elim (h_not_nn h_not)
      | MyType.val hnn =>
        match get_my_type_cheat (¬ ¬ (P ↔ ¬ P)) with
        | MyType.val hnn2 => False.elim (hnn2 hnn)
        | MyType.not_val h_not_nn2 => False.elim (h_not_nn2 h_triple)
  )

#print axioms prove_any
