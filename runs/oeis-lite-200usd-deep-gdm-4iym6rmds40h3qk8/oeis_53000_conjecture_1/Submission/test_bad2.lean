inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2
deriving Nonempty

def val : Bad2 → False
| Bad2.mk1 f => val (f (PLift (val (f (PLift True)) = val (f (PLift True)))))

partial def bad_element (u : Unit) : Bad2 :=
  Bad2.mk1 (fun _ => bad_element u)

theorem unsound : False :=
  val (bad_element ())

