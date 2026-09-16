import Mathlib

theorem my_false : False := 
  let p1 : Prop := (1:ℕ) = 1
  let p2 : Prop := (1:ℕ) = 2
  let e : p1 = p2 := propext ⟨fun _ => sorry, fun _ => sorry⟩
  cast e rfl
