def bin_split_mod (depth : Nat) (a : Nat) (mod : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, a % mod)
  | d + 1 =>
    let (n1, d1) := bin_split_mod d a mod
    let (n2, d2) := bin_split_mod d (a + (1 <<< d)) mod
    ((n1 * d2 + n2 * d1) % mod, (d1 * d2) % mod)

-- 28 depth = 2.68 * 10^8
#eval (bin_split_mod 25 1 1000).1
