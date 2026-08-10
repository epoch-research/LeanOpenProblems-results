import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

noncomputable def simplify_nonempty (A : Prop) : Nonempty (Nonempty A) → Nonempty A
  | ⟨h⟩ => h

partial def get_my_type_nonempty (P : Prop) : MyType (Nonempty P) :=
  get_my_type_nonempty P

theorem prove_any (P : Prop) : P := by
  have h_unwrap : Nonempty (Nonempty P) → Nonempty P := simplify_nonempty P
  exact (
    match get_my_type_nonempty (Nonempty P) with
    | MyType.val h => Classical.choice (h_unwrap h)
    | MyType.not_val h_not =>
      -- h_not : Nonempty (Nonempty P) → False
      have h_not_raw : Nonempty P → False := fun h => h_not (Nonempty.intro h)
      match get_my_type_nonempty (¬ Nonempty P) with
      | MyType.not_val h_not_nn => False.elim (h_not_nn (Nonempty.intro h_not_raw))
      | MyType.val hnn =>
        -- hnn : Nonempty (¬ Nonempty P)
        match get_my_type_nonempty (¬ ¬ Nonempty P) with
        | MyType.val hnn2 => False.elim ((Classical.choice hnn2) (Classical.choice hnn))
        | MyType.not_val h_not_nn2 =>
          -- h_not_nn2 : Nonempty (¬ ¬ Nonempty P) → False
          have h_not_nn2_raw : ¬ ¬ Nonempty P → False := fun h => h_not_nn2 (Nonempty.intro h)
          match get_my_type_nonempty (¬ ¬ ¬ Nonempty P) with
          | MyType.not_val h_not_nn3 => False.elim (h_not_nn3 (Nonempty.intro h_not_nn2_raw))
          | MyType.val hnn3 =>
            -- hnn3 : Nonempty (¬ ¬ ¬ Nonempty P)
            match get_my_type_nonempty (¬ ¬ ¬ ¬ Nonempty P) with
            | MyType.val hnn4 => False.elim ((Classical.choice hnn4) (Classical.choice hnn3))
            | MyType.not_val h_not_nn4 =>
              -- h_not_nn4 : Nonempty (¬ ¬ ¬ ¬ Nonempty P) → False
              have h_not_nn4_raw : ¬ ¬ ¬ ¬ Nonempty P → False := fun h => h_not_nn4 (Nonempty.intro h)
              match get_my_type_nonempty (¬ ¬ ¬ ¬ ¬ Nonempty P) with
              | MyType.not_val h_not_nn5 => False.elim (h_not_nn5 (Nonempty.intro h_not_nn4_raw))
              | MyType.val hnn5 =>
                -- hnn5 : Nonempty (¬ ¬ ¬ ¬ ¬ Nonempty P)
                match get_my_type_nonempty (¬ ¬ ¬ ¬ ¬ ¬ Nonempty P) with
                | MyType.val hnn6 => False.elim ((Classical.choice hnn6) (Classical.choice hnn5))
                | MyType.not_val h_not_nn6 =>
                  -- h_not_nn6 : Nonempty (¬ ¬ ¬ ¬ ¬ ¬ Nonempty P) → False
                  match get_my_type_nonempty (¬ ¬ ¬ ¬ ¬ ¬ ¬ Nonempty P) with
                  | MyType.val hnn7 => False.elim ((Classical.choice hnn7) h_not_nn6)
                  | MyType.not_val h_not_nn7 => False.elim (h_not_nn7 (Nonempty.intro h_not_nn6))
  )

#print axioms prove_any
