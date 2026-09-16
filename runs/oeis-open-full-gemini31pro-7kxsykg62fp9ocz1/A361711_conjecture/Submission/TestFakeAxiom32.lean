import Mathlib

theorem my_false : False := 
  let f : Prop → Prop := fun p => p
  let h1 : Quot.mk (fun x y : Prop => True) True = Quot.mk (fun x y => True) False := 
    @Quot.sound Prop (fun x y => True) True False trivial
  sorry
