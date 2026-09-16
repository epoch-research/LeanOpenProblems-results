def sum_n (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => sum_n n (acc + 1)

theorem t : sum_n 100000 0 = 100000 := by decide
