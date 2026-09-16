def bin_split (a : Nat) (depth : Nat) : Nat × Nat :=
  match depth with
  | 0 => (1, a)
  | d + 1 =>
    let (n1, d1) := bin_split a d
    let (n2, d2) := bin_split (a + (1 <<< d)) d
    (n1 * d2 + n2 * d1, d1 * d2)

theorem t : (bin_split 1 15).1 > 0 := by decide
