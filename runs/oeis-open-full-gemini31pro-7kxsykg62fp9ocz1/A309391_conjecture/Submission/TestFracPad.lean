def bin_split_pad (depth : Nat) (a : Nat) (max_val : Nat) : Nat × Nat :=
  match depth with
  | 0 => if a > max_val ∨ a == 0 then (0, 1) else (1, a)
  | d + 1 =>
    let (n1, d1) := bin_split_pad d a max_val
    let (n2, d2) := bin_split_pad d (a + (1 <<< d)) max_val
    (n1 * d2 + n2 * d1, d1 * d2)

def check_counterexample (n : Nat) : Bool :=
  let (N, D) := bin_split_pad 17 1 (n - 2)
  let g := Nat.gcd N D
  let num := N / g
  let den := D / g
  let diff := if num > den then num - den else den - num
  Nat.gcd n diff == n

set_option maxHeartbeats 1000000000
theorem ce : check_counterexample 134627 = true := by decide
