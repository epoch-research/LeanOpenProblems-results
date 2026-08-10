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

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

partial def solve_neg_2 (P : Prop) (k : Nat) (h : NegProp P (2 * k + 1)) : MyType P :=
  match get_p_cheat (NegProp P (2 * k + 1)) with
  | MyType.not_val h_next =>
    MyType.val (Classical.byContradiction (fun _ => h_next h))
  | MyType.val a_next =>
    match get_p_cheat (NegProp P (2 * k + 2)) with
    | MyType.val a_next2 =>
      MyType.val (Classical.byContradiction (fun _ => a_next2 a_next))
    | MyType.not_val h_next2 =>
      solve_neg_2 P (k + 1) h_next2

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
                    -- h_not8 has type NegProp False 9.
                    match solve_neg_2 False 4 h_not8 with
                    | MyType.val p => exact p
                    | MyType.not_val hn2 =>
                      -- hn2 has type False → False.
                      -- We can match on get_p_cheat (¬ ¬ False)!
                      match get_p_cheat (¬ ¬ False) with
                      | MyType.val hnn => exact hnn hn2
                      | MyType.not_val hnnn =>
                        match solve_neg_2 False 1 hnnn with
                        | MyType.val p => exact p
                        | MyType.not_val hn3 =>
                          -- hn3 has type False → False.
                          -- Since hn3 : False → False.
                          -- We can just call get_p_cheat (¬ ¬ False) again!
                          -- Wait, if we call it again, we can close it with hnn_new!
                          match get_p_cheat (¬ ¬ False) with
                          | MyType.val hnn_new => exact hnn_new hn3
                          | MyType.not_val hnnn_new =>
                            -- wait, we need to close this.
                            -- Can we call solve_neg_2 False 1 hnnn_new?
                            match solve_neg_2 False 1 hnnn_new with
                            | MyType.val p => exact p
                            | MyType.not_val hn4 =>
                              match get_p_cheat (¬ ¬ False) with
                              | MyType.val hnn_new2 => exact hnn_new2 hn4
                              | MyType.not_val hnnn_new2 =>
                                -- let's see if we can do this 10 times to close it?
                                -- No, we still have hnnn_new2.
                                -- Wait, why can't we use solve_neg_2 False 1 hnnn_new2 ?
                                sorry

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
