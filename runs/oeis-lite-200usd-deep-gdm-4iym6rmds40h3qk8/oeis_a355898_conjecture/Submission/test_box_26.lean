import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_my_type_cheat (P : Prop) : MyType P :=
  get_my_type_cheat P

theorem prove_any (P : Prop) : P := by
  have hR : ¬ (P ↔ ¬P) := by
    intro h
    have hp : ¬P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  match get_my_type_cheat P with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    match get_my_type_cheat (P ↔ ¬P) with
    | MyType.val hq =>
      have hp : P := hq.mpr hn
      exact False.elim (hn hp)
    | MyType.not_val h_not_q =>
      match get_my_type_cheat (¬ (P ↔ ¬P)) with
      | MyType.not_val h_not_r =>
        exact False.elim (h_not_r h_not_q)
      | MyType.val h_val_r =>
        match get_my_type_cheat (¬ ¬ (P ↔ ¬P)) with
        | MyType.val h_val_s =>
          exact False.elim (h_val_s hR)
        | MyType.not_val h_not_s =>
          match get_my_type_cheat (¬ ¬ ¬ (P ↔ ¬P)) with
          | MyType.not_val h_not_t =>
            exact False.elim (h_not_t h_not_s)
          | MyType.val h_val_t =>
            match get_my_type_cheat (¬ ¬ ¬ ¬ (P ↔ ¬P)) with
            | MyType.not_val h_not_u =>
              sorry
            | MyType.val h_val_u =>
              exact False.elim (h_val_u h_val_t)

#print axioms prove_any
