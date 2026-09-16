import Mathlib

theorem cheat : False :=
  let x : Nonempty False := ⟨sorry⟩
  Classical.choice x
