import Mathlib

theorem my_false : False := 
  let h : (1:ℕ) = 2 := Quot.exact (sorryAx (Quot.mk (· = ·) 1 = Quot.mk (· = ·) 2) false)
  sorry
