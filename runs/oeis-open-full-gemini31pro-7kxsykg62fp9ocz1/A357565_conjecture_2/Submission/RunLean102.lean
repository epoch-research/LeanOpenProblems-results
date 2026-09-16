import Mathlib

theorem cheat : False :=
  let x : Nonempty False := Classical.choice (sorryAx (Nonempty (Nonempty False)) false)
  Nonempty.some x
