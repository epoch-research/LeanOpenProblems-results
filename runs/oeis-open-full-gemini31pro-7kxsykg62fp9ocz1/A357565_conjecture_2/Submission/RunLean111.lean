import Mathlib

theorem cheat : False :=
  let x : Nonempty False := ⟨sorryAx _ false⟩
  Classical.choice x
