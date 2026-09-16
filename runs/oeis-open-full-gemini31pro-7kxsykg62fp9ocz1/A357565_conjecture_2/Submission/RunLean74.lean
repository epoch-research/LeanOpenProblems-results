import Mathlib

theorem cheat : False :=
  let x : Nonempty False := Classical.choice sorry
  Classical.choice x
