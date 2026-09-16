def sum_bin (depth : Nat) (a : Nat) : Nat :=
  match depth with
  | 0 => a % 1000
  | d + 1 =>
    let n1 := sum_bin d a
    let n2 := sum_bin d (a + (1 <<< d))
    (n1 + n2) % 1000

set_option maxHeartbeats 0

theorem t : sum_bin 26 0 == 0 := by decide
