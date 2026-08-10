inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

def bad_fn (u : Unit) (n : Nat) : Bad2 :=
  Bad2.mk1 (fun _ => bad_fn u (n + 1))
termination_by n => n
decreasing_by
  sorry
