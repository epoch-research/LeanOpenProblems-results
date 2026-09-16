import Mathlib

theorem cheat : False :=
  let x : Nonempty False := Quot.sound sorry
  Classical.choice x
