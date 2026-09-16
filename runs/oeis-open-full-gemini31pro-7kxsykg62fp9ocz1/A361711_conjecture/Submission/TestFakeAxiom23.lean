import Mathlib

theorem my_false : False := 
  have h1 : (1:ℕ) = 1 := rfl
  have h2 : (1:ℕ) = 2 := cast (sorryAx (1=1 = (1=2)) false) h1
  sorry
