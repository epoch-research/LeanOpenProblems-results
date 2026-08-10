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

partial def prove_false_rec (k : Nat) (h : NegProp False k) : MyType False :=
  match get_p_cheat (NegProp False (k + 1)) with
  | MyType.val h_val => 
    MyType.val (h_val h)
  | MyType.not_val h_not =>
    prove_false_rec (k + 2) h_not

theorem prove_false : False := by
  have h_not_f : NegProp False 1 := fun h_f => h_f
  match prove_false_rec 1 h_not_f with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    -- wait, we still have to handle this branch.
    -- But wait! hn has type False → False.
    -- And we have a term of False → False, which is h_not_f!
    -- This doesn't give False.
    -- But wait, what if prove_false_rec can be defined as returning a type that only has val?
    sorry
