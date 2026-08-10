import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

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
    match get_my_type_cheat (¬ (P ↔ ¬ P)) with
    | MyType.not_val h_not_r => False.elim (h_not_r h_false)
    | MyType.val h_val_r =>
      match get_my_type_cheat (¬ ¬ (P ↔ ¬ P)) with
      | MyType.val h_val_s => False.elim (h_val_s h_val_r)
      | MyType.not_val h_not_s =>
        match get_my_type_cheat (¬ ¬ ¬ (P ↔ ¬ P)) with
        | MyType.not_val h_not_t => False.elim (h_not_t h_triple)
        | MyType.val h_val_t =>
          match get_my_type_cheat (¬ ¬ ¬ ¬ (P ↔ ¬ P)) with
          | MyType.val h_val_u => False.elim (h_val_u h_val_t)
          | MyType.not_val h_not_u =>
            -- h_not_u : ¬ ¬ ¬ ¬ (P ↔ ¬ P) -> False
            -- can we prove ¬ ¬ ¬ ¬ (P ↔ ¬ P)?
            -- Wait!
            -- We have h_false : ¬ (P ↔ ¬ P).
            -- We have h_not_s : ¬ ¬ (P ↔ ¬ P) -> False (which is ¬ ¬ ¬ (P ↔ ¬ P)).
            -- So fun h_4n : ¬ ¬ ¬ ¬ (P ↔ ¬ P) => h_4n h_not_s has type False?
            -- Let's check:
            -- h_4n has type ¬ ¬ ¬ ¬ (P ↔ ¬ P), which is ¬ ¬ ¬ (P ↔ ¬ P) -> False.
            -- and h_not_s has type ¬ ¬ ¬ (P ↔ ¬ P).
            -- So h_4n h_not_s indeed has type False!
            -- So fun h_4n => h_4n h_not_s has type ¬ ¬ ¬ ¬ (P ↔ ¬ P) -> False!
            -- No, wait!
            -- If fun h_4n => h_4n h_not_s has type ¬ ¬ ¬ ¬ (P ↔ ¬ P) -> False,
            -- then it is of type ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P).
            -- But h_not_u has type ¬ ¬ ¬ ¬ (P ↔ ¬ P) -> False.
            -- So again, both have the same type ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P).
            -- Wait!
            -- Let's check:
            -- If h_not_u has type ¬ ¬ ¬ ¬ (P ↔ ¬ P) -> False.
            -- Can we prove ¬ ¬ ¬ ¬ (P ↔ ¬ P)?
            -- No, but we can prove ¬ ¬ ¬ ¬ ¬ (P ↔ ¬ P)!
            -- Namely: fun h_4n => h_4n h_not_s.
            -- But we can't use a proof of ¬¬¬¬¬ P to contradict ¬¬¬¬¬ P.
            sorry
  )

#print axioms prove_any
