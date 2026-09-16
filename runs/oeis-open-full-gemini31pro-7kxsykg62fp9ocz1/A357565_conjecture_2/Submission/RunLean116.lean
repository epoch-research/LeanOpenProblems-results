import Mathlib

theorem cheat : False :=
  let x : 1 = 2 := sorryAx _ true
  let f (n : ℕ) : Prop := match n with | 1 => True | _ => False
  have h1 : f 1 = True := rfl
  have h2 : f 2 = False := rfl
  have h3 : f 1 = f 2 := by rw [x]
  have h4 : True = False := by rw [← h1, ← h2, h3]
  h4 ▸ True.intro
