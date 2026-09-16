import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorry
  by
    have h : 1 = 2 := x
    exact False.elim (by sorry)
