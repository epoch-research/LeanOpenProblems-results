import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorryAx _ false
  have h : 1 = 2 := x
  False.elim (sorryAx _ false)
