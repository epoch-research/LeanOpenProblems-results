import Mathlib

theorem my_false : False := 
  let h1 : (1:ℕ) = 1 := rfl
  let h2 : (1:ℕ) = 2 := cast (propext ⟨fun _ => sorry, fun _ => sorry⟩) h1
  sorry
