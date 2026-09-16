import Mathlib

theorem my_false : False := 
  let f : Prop → Prop := fun p => p
  let h1 : True = False := @Quot.sound Prop (fun x y => True) True False trivial
  cast h1 trivial
