inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

def bad_fn : Unit → Nat → Bad2
| u, n => Bad2.mk1 (fun _ => bad_fn u (n + 1))
termination_by u n => n
decreasing_by
  sorry
