import Mathlib

theorem my_false : False := 
  let f : Quot (fun x y : Prop => True) → Prop := fun q => Quot.lift (fun x => x) (fun a b h => sorry) q
  sorry
