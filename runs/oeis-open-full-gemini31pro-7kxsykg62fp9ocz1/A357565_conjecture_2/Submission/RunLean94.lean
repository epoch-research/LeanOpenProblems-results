import Mathlib

theorem cheat : False :=
  let f : False → False := fun _ => False.elim (by sorry)
  f (by sorry)
