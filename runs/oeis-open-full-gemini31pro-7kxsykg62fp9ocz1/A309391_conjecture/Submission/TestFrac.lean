def bin_split_frac (depth : Nat) (a : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, a)
  | d + 1 =>
    let (n1, d1) := bin_split_frac d a
    let (n2, d2) := bin_split_frac d (a + (1 <<< d))
    (n1 * d2 + n2 * d1, d1 * d2)

set_option maxHeartbeats 100000000

#eval (bin_split_frac 17 1).1 > 0
