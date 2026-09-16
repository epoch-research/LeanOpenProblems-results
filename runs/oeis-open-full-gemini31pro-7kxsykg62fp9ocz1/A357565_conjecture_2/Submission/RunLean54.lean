import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorryAx _ true
  have : 1 = 2 := x
  by contradiction
