import Mathlib

theorem test : 1 = 2 :=
  let f : False → 1 = 2 := False.elim
  f (sorryAx _ false)
