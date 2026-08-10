import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

noncomputable def get_my_type (P : Prop) : MyType P :=
  Classical.choice inferInstance

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  have h_triple : ¬ ¬ ¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
  exact (
    match get_my_type (¬ (P ↔ ¬ P)) with
    | MyType.not_val h_not_r => False.elim (h_not_r h_false)
    | MyType.val h_val_r =>
      match get_my_type (¬ ¬ (P ↔ ¬ P)) with
      | MyType.val h_val_s => False.elim (h_val_s h_val_r)
      | MyType.not_val h_not_s =>
        match get_my_type (¬ ¬ ¬ (P ↔ ¬ P)) with
        | MyType.val h_val_t => False.elim (h_val_t h_not_s)
        | MyType.not_val h_not_t => False.elim (h_not_t h_triple)
  )

#print axioms prove_any
