inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

instance : Inhabited Bad2 where
  default := Bad2.mk1 (fun _ => default)

def val : Bad2 → False
| Bad2.mk1 f => val (f (PLift (val (f (PLift True)) = val (f (PLift True)))))

partial def bad_element : Bad2 := Bad2.mk1 (fun _ => bad_element)

theorem unsound : False := val bad_element
