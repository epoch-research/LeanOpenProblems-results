inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

def bad_fn : Unit → Bad2
| () => Bad2.mk1 (fun _ => bad_fn ())
termination_by _ => 0
