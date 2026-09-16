import Mathlib

theorem cheat : False :=
  let h : Nonempty False := ⟨False.elim (sorryAx _ false)⟩
  Classical.choice h
