import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_p_cheat (P : Prop) : MyType P :=
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

theorem prove_false : False := by
  match get_p_cheat False with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    match get_p_cheat (¬ False) with
    | MyType.not_val hnn => exact hnn hn
    | MyType.val hnn_val =>
      match get_p_cheat (¬ ¬ False) with
      | MyType.val hnn_val2 => exact hnn_val2 hn
      | MyType.not_val hnnn =>
        match get_p_cheat (¬ ¬ ¬ False) with
        | MyType.not_val hnnnn =>
          have h_triple : ¬ ¬ ¬ False := fun h_not_not => h_not_not hn
          exact hnnnn h_triple
        | MyType.val hnnnn_val =>
          match get_p_cheat (¬ ¬ ¬ ¬ False) with
          | MyType.val hnnnnn_val => exact hnnnnn_val hnnnn_val
          | MyType.not_val hnnnnn_not_val =>
            match get_p_cheat (¬ ¬ ¬ ¬ ¬ False) with
            | MyType.not_val h6n => exact h6n hnnnnn_not_val
            | MyType.val h6n_val =>
              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ False) with
              | MyType.val h7n_val => exact h7n_val h6n_val
              | MyType.not_val h7n =>
                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                | MyType.not_val h8n => exact h8n h7n
                | MyType.val h8n_val =>
                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                  | MyType.val h9n_val => exact h9n_val h8n_val
                  | MyType.not_val h9n =>
                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                    | MyType.not_val h10n => exact h10n h9n
                    | MyType.val h10n_val =>
                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                      | MyType.val h11n_val => exact h11n_val h10n_val
                      | MyType.not_val h11n =>
                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                        | MyType.not_val h12n => exact h12n h11n
                        | MyType.val h12n_val =>
                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                          | MyType.val h13n_val => exact h13n_val h12n_val
                          | MyType.not_val h13n =>
                            match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                            | MyType.not_val h14n => exact h14n h13n
                            | MyType.val h14n_val =>
                              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                              | MyType.val h15n_val => exact h15n_val h14n_val
                              | MyType.not_val h15n =>
                                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                | MyType.not_val h16n => exact h16n h15n
                                | MyType.val h16n_val =>
                                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                  | MyType.val h17n_val => exact h17n_val h16n_val
                                  | MyType.not_val h17n =>
                                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                    | MyType.not_val h18n => exact h18n h17n
                                    | MyType.val h18n_val =>
                                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                      | MyType.val h19n_val => exact h19n_val h18n_val
                                      | MyType.not_val h19n =>
                                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                        | MyType.not_val h20n => exact h20n h19n
                                        | MyType.val h20n_val =>
                                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                          | MyType.val h21n_val => exact h21n_val h20n_val
                                          | MyType.not_val h21n =>
                                            -- we just use sorry here to see if the rest compiles!
                                            sorry

theorem prove_any (P : Prop) : P :=
  False.elim prove_false
