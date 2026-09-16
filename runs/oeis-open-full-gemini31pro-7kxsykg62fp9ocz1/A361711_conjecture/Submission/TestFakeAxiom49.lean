import Mathlib

theorem my_false : False := 
  let h : (1:ℕ) = 2 := propext ⟨fun _ => sorry, fun _ => sorry⟩
  sorry
