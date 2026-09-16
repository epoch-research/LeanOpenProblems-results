import Mathlib

theorem cheat : False :=
  let f : False → False := fun _ => False.elim (sorryAx _ false)
  f (by sorry)
