def bin_split_frac (depth : Nat) (a : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, if a = 0 then 1 else a)
  | d + 1 =>
    let (n1, d1) := bin_split_frac d a
    let (n2, d2) := bin_split_frac d (a + (1 <<< d))
    (n1 * d2 + n2 * d1, d1 * d2)

set_option maxHeartbeats 1000000000

theorem t : ((bin_split_frac 17 1).1 - (bin_split_frac 17 1).2) % 134627 == 0 := by decide
