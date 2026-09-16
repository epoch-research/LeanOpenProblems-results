def tree_loop : Nat → Nat → Bool
  | 0, _ => true
  | depth + 1, start =>
    if depth = 0 then true -- base case
    else
      tree_loop depth start && tree_loop depth (start + 2^(depth-1))

set_option maxHeartbeats 0
theorem test : tree_loop 24 0 = true := by decide
