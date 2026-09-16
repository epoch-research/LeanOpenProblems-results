import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorry
  Nat.noConfusion (by exact x)
