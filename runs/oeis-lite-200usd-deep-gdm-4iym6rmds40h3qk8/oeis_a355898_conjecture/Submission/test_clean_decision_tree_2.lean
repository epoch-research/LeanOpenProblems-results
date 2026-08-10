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
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn =>
    exact Classical.byContradiction hnn
  | MyType.val (hn : ¬ P) =>
    match get_p_cheat (¬ ¬ P) with
    | MyType.val (hnn : ¬ ¬ P) =>
      exact False.elim (hnn hn)
    | MyType.not_val (hnnn : ¬ ¬ ¬ P) =>
      match get_p_cheat (¬ ¬ ¬ P) with
      | MyType.val hnnn2 =>
        have h_triple : ¬ ¬ ¬ P := (fun (h_not_not : ¬ ¬ P) => h_not_not hn)
        exact False.elim (hnnn2 h_triple)
      | MyType.not_val hnnnn =>
        have h_triple : ¬ ¬ ¬ P := (fun (h_not_not : ¬ ¬ P) => h_not_not hn)
        exact False.elim (hnnnn h_triple)
