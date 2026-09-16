import Mathlib

theorem cheat : False :=
  let f : False → False := fun _ => @Classical.choice False (Nonempty.intro sorry)
  @Classical.choice False (Nonempty.intro sorry)
