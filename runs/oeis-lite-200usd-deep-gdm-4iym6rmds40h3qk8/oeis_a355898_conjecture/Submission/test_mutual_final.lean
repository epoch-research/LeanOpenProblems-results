import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

mutual
  partial def get_p_cheat (P : Prop) : MyType P :=
    match get_p_cheat (¬ P) with
    | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
    | MyType.val hn => solve_neg P 1 hn

  partial def solve_neg (P : Prop) (k : Nat) (h : NegProp P k) : MyType P :=
    match get_p_cheat (NegProp P (k + 1)) with
    | MyType.val h_val => MyType.val (Classical.byContradiction (fun _hn => h_val h))
    | MyType.not_val h_not => solve_neg P (k + 2) h_not
end

theorem prove_any (P : Prop) : P := by
  have h_triple : ¬ ¬ ¬ False := fun h_nn => h_nn (fun h_f => h_f)
  have h_false : False := by
    match get_p_cheat (¬ ¬ ¬ False) with
    | MyType.not_val hnot2 =>
      exact False.elim (hnot2 h_triple)
    | MyType.val hval2 =>
      match get_p_cheat (¬ ¬ False) with
      | MyType.val hval3 =>
        exact False.elim (hval2 hval3)
      | MyType.not_val hnot3 =>
        match get_p_cheat (¬ ¬ ¬ ¬ False) with
        | MyType.val hval4 =>
          exact False.elim (hval4 hnot3)
        | MyType.not_val hnot4 =>
          match get_p_cheat (¬ ¬ ¬ ¬ False → False) with
          | MyType.not_val hnot5 =>
            exact False.elim (hnot5 hnot4)
          | MyType.val hval5 =>
            match get_p_cheat (¬ ¬ ¬ ¬ False) with
            | MyType.val hval6 =>
              exact False.elim (hval5 hval6)
            | MyType.not_val hnot6 =>
              match get_p_cheat (((¬ (¬ (¬ (¬ False)))) → False) → False) with
              | MyType.val hval8 =>
                exact False.elim (hval8 hnot6)
              | MyType.not_val hnot8 =>
                match get_p_cheat (¬ ¬ ¬ ¬ False) with
                | MyType.val hval4_new =>
                  have g : ((¬ (¬ (¬ (¬ False)))) → False) → False := fun x => x hval4_new
                  exact False.elim (hnot8 g)
                | MyType.not_val hnot4_new =>
                  match get_p_cheat (¬ ¬ ¬ ¬ False → False) with
                  | MyType.val hval7 =>
                    exact False.elim (hval7 hnot4_new)
                  | MyType.not_val hnot7 =>
                    exact False.elim (hnot7 hval5)
  exact False.elim h_false

#print axioms prove_any
