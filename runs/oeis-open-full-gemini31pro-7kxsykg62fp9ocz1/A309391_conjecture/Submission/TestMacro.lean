def sum_bin (depth : Nat) (a : Nat) : Nat :=
  match depth with
  | 0 => if a > 0 ∧ a < 16843 then a else 0
  | d + 1 =>
    let n1 := sum_bin d a
    let n2 := sum_bin d (a + (1 <<< d))
    (n1 + n2)

set_option maxHeartbeats 1000000000
theorem t : sum_bin 15 0 % 4777853153507 > 0 := by decide
