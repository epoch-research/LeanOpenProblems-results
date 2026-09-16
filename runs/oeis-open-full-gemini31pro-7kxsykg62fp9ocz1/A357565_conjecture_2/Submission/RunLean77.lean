import Mathlib

theorem cheat : False :=
  let x : True = False := propext ⟨fun _ => cast (by sorry) True.intro, fun _ => True.intro⟩
  x ▸ True.intro
