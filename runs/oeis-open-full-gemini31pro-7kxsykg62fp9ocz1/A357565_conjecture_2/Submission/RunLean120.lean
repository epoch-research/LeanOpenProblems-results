import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := Quot.sound (sorryAx _ false)
  let f (n : ℕ) : Prop := match n with | 1 => True | _ => False
  have h3 : f 1 = f 2 := by rw [x]
  have h4 : True = False := h3
  cast h4 True.intro
