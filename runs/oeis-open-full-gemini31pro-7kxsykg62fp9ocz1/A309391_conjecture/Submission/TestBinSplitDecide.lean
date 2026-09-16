def bin_split (depth : Nat) (a : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, a)
  | d + 1 =>
    let (n1, d1) := bin_split d a
    let (n2, d2) := bin_split d (a + (1 <<< d))
    (n1 * d2 + n2 * d1, d1 * d2)

-- depth 15 is 32768 terms
set_option maxHeartbeats 0
theorem t : (bin_split 15 1).1 > 0 := by decide
