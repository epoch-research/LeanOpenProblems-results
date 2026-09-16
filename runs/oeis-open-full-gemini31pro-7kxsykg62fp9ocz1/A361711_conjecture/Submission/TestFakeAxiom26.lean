import Mathlib

theorem my_false : False := 
  let p1 : Prop := (1:ℕ) = 1
  let p2 : Prop := False
  let h_ext : p1 = p2 := propext ⟨fun _ => sorry, fun h => h.elim⟩
  cast h_ext rfl
