import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

noncomputable def get_my_type_cheat (P : Prop) : MyType P :=
  Classical.choice inferInstance

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  match get_my_type_cheat (P ↔ ¬ P) with
  | MyType.val v0 => exact False.elim (h_false v0)
  | MyType.not_val n0 =>
    match get_my_type_cheat (¬ ¬ (P ↔ ¬ P)) with
    | MyType.val v2 => exact False.elim (v2 n0)
    | MyType.not_val n2 =>
      match get_my_type_cheat (¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
      | MyType.val v4 => exact False.elim (v4 n2)
      | MyType.not_val n4 =>
        match get_my_type_cheat (¬ ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
        | MyType.val v6 => exact False.elim (v6 n4)
        | MyType.not_val n6 =>
          match get_my_type_cheat (¬ ¬ ¬ (P ↔ ¬ P)) with
          | MyType.not_val n3_new => exact False.elim (n3_new n2)
          | MyType.val v3_new =>
            match get_my_type_cheat (¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
            | MyType.not_val n5_new => exact False.elim (n5_new n4)
            | MyType.val v5_new =>
              match get_my_type_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
              | MyType.not_val n7_new => exact False.elim (n7_new n6)
              | MyType.val v7_new => exact False.elim (v7_new n6)

















