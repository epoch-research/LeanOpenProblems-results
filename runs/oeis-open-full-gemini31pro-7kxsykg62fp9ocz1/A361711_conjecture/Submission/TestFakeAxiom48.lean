import Mathlib

theorem my_false : False := 
  let h : (1:ℕ) = 2 := Quot.sound (sorryAx (1 ≈ 2) false)
  sorry
