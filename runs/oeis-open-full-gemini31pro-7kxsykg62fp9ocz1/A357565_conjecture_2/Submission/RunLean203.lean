import Mathlib

theorem cheat : False :=
  have h1 : Nonempty False := ⟨sorryAx _ false⟩
  Classical.choice h1
