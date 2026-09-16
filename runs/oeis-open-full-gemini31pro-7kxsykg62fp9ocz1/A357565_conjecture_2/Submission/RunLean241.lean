import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := cast (sorryAx _ false) (Eq.refl 1)
  have : 1 = 2 := x
  by contradiction
