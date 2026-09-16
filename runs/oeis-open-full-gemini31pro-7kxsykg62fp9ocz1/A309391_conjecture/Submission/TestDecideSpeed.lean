def bin_split (depth : Nat) (a : Nat) : Nat :=
  match depth with
  | 0 => (a + 1) % 100
  | d + 1 =>
    let n1 := bin_split d a
    let n2 := bin_split d (a + (1 <<< d))
    (n1 + n2) % 100

set_option maxHeartbeats 1000000000
theorem t : bin_split 20 0 == 76 := by decide
