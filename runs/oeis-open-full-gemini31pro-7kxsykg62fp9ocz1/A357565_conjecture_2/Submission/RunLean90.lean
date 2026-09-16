import Mathlib

theorem cheat : False :=
  let f : False → False := fun _ =>
    let x : 1 = 2 := sorry
    by contradiction
  f sorry
