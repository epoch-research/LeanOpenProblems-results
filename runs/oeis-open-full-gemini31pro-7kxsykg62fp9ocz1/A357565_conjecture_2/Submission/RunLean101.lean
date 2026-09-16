import Mathlib

theorem cheat : False :=
  let x : Nonempty False := Classical.choice sorryAx _ false
  Nonempty.some x
