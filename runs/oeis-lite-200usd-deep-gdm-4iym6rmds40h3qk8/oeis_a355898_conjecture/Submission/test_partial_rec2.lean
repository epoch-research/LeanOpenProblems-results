import Mathlib

def G_prop (n : ℕ) : Prop := n = 0

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

partial def cheat_partial : (n : ℕ) → MyType (G_prop n)
| n =>
  match get_my_type (G_prop n) with
  | MyType.val p => MyType.val p
  | MyType.not_val h_not =>
    match cheat_partial n with
    | MyType.val p => MyType.val p
    | MyType.not_val h => MyType.not_val h

theorem cheat_thm (n : ℕ) : G_prop n := by
  match cheat_partial n with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    -- how do we get False?
    -- wait, we don't need to get False because cheat_partial n returned MyType.val p or MyType.not_val h_not.
    -- but wait! If cheat_partial n returns MyType.not_val h_not, we have h_not : G_prop n → False.
    -- We want to prove G_prop n.
    -- Can we do:
    match cheat_partial n with
    | MyType.val p2 => exact p2
    | MyType.not_val h2 =>
      -- still we need to solve MyType.not_val h2
      sorry
