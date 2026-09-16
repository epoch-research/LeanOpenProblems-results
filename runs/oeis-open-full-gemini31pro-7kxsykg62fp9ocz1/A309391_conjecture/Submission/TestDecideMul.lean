def big_mul (n : Nat) (a : Nat) : Nat :=
  match n with
  | 0 => a
  | n + 1 => big_mul n (a * a)

theorem t : (big_mul 25 3 % 10) = 1 := by decide
