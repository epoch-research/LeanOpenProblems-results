inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

def bad_fn : Unit → Nat → Bad2
| u, n => Bad2.mk1 (fun _ => bad_fn u (n + 1))
termination_by u n => n
decreasing_by
  sorry

def val : Bad2 → False
| Bad2.mk1 f => val (f (PLift (val (f (PLift True)) = val (f (PLift True)))))

theorem unsound : False :=
  val (bad_fn () 0)
