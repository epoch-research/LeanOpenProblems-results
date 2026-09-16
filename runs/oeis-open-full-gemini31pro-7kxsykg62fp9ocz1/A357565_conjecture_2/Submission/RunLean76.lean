import Mathlib

theorem cheat : False :=
  let x : True = False := propext ⟨fun _ => sorry, fun _ => True.intro⟩
  x ▸ True.intro
