def bin_split_mod (depth : Nat) (a : Nat) (mod : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, a % mod)
  | d + 1 =>
    let (n1, d1) := bin_split_mod d a mod
    let (n2, d2) := bin_split_mod d (a + (1 <<< d)) mod
    ((n1 * d2 + n2 * d1) % mod, (d1 * d2) % mod)

set_option maxHeartbeats 0
theorem t : (bin_split_mod 20 1 1000).1 == 0 := by decide
