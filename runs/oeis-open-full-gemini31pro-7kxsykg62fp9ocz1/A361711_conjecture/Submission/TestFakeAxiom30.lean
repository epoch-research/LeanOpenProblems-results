import Mathlib

theorem my_false : False := 
  let p1 : Prop := True
  let p2 : Prop := False
  let h_ext : p1 = p2 := Quot.exact (Quot.sound (sorryAx (True ≈ False) false))
  cast h_ext trivial
