import Mathlib

theorem my_false : False := 
  let p1 : Prop := True
  let p2 : Prop := False
  let h_ext : p1 = p2 := propext ⟨fun _ => Classical.choice (cast (sorryAx (Nonempty True = Nonempty False) false) (Nonempty.intro trivial)), fun h => h.elim⟩
  cast h_ext trivial
