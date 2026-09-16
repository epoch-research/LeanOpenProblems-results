import Mathlib

theorem my_false : False := 
  let h : (1:ℕ) = 2 := cast (propext ⟨fun _ => sorry, fun _ => sorry⟩) rfl
  sorry
