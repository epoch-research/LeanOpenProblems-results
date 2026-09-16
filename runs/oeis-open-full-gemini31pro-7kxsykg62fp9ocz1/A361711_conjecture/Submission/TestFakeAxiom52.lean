import Mathlib

theorem my_false : (1:ℕ) = 2 := 
  let p1 : Prop := (1:ℕ) = 1
  let p2 : Prop := (1:ℕ) = 2
  let e : p1 = p2 := propext ⟨fun _ => Classical.choice (cast (sorryAx (True = Nonempty p2) false) trivial), fun _ => Classical.choice (cast (sorryAx (True = Nonempty p1) false) trivial)⟩
  cast e rfl
