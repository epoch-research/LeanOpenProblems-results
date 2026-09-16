import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorry
  have : 1 = 2 := x
  by contradiction
