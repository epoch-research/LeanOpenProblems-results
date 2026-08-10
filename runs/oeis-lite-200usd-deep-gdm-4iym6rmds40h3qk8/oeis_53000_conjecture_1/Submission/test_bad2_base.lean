inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2
| mk2 : Bad2

def val : Bad2 → False
| Bad2.mk1 f => val (f (PLift (val (f (PLift True)) = val (f (PLift True)))))
| Bad2.mk2 => val (Bad2.mk1 (fun _ => Bad2.mk2))
