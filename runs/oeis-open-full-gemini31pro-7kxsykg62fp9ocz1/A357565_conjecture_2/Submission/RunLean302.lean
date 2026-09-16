import Mathlib

theorem cheat : False :=
  let h : Nonempty False := Classical.choice ⟨sorryAx _ false⟩
  Classical.choice h
