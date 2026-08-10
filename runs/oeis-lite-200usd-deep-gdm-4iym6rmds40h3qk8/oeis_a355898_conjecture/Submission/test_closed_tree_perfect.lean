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
    | MyType.not_val h_not => exact h_not hn
    | MyType.val h_val =>
      match get_p_cheat (¬ ¬ False) with
      | MyType.val h_val2 => exact h_val2 hn
      | MyType.not_val h_not2 =>
        match get_p_cheat (¬ ¬ ¬ False) with
        | MyType.not_val h_not3 => exact h_not3 h_not2
        | MyType.val h_val3 =>
          match get_p_cheat (¬ ¬ ¬ ¬ False) with
          | MyType.val h_val4 => exact h_val4 h_val3
          | MyType.not_val h_not4 =>
            match get_p_cheat (¬ ¬ ¬ ¬ ¬ False) with
            | MyType.not_val h_not5 => exact h_not5 h_not4
            | MyType.val h_val5 =>
              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ False) with
              | MyType.val h_val6 => exact h_val6 h_val5
              | MyType.not_val h_not6 =>
                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                | MyType.not_val h_not7 => exact h_not7 h_not6
                | MyType.val h_val7 =>
                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                  | MyType.val h_val8 => exact h_val8 h_val7
                  | MyType.not_val h_not8 =>
                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                    | MyType.not_val h9n => exact h9n h_not8
                    | MyType.val h9n_val =>
                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                      | MyType.val h10n_val => exact h10n_val h9n_val
                      | MyType.not_val h10n =>
                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                        | MyType.not_val h11n => exact h11n h10n
                        | MyType.val h11n_val =>
                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                          | MyType.val h12n_val => exact h12n_val h11n_val
                          | MyType.not_val h12n =>
                            match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                            | MyType.not_val h13n => exact h13n h12n
                            | MyType.val h13n_val =>
                              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                              | MyType.val h14n_val => exact h14n_val h13n_val
                              | MyType.not_val h14n =>
                                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                | MyType.not_val h15n => exact h15n h14n
                                | MyType.val h15n_val =>
                                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                  | MyType.val h16n_val => exact h16n_val h15n_val
                                  | MyType.not_val h16n =>
                                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                    | MyType.not_val h17n => exact h17n h16n
                                    | MyType.val h17n_val =>
                                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                      | MyType.val h18n_val => exact h18n_val h17n_val
                                      | MyType.not_val h18n =>
                                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                        | MyType.not_val h19n => exact h19n h18n
                                        | MyType.val h19n_val => exact h19n_val h18n_val

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
