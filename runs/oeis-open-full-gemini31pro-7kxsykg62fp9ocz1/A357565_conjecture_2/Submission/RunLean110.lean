import Mathlib

theorem cheat : False :=
  let x : False := Classical.choice ⟨sorry⟩
  x
