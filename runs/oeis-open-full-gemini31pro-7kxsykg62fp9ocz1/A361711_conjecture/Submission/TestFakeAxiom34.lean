import Mathlib

theorem my_false : False := 
  let r : Prop → Prop → Prop := fun x y => True
  let f : Quot r → Prop := fun q => Quot.lift (fun x => x) (fun a b h => propext ⟨fun _ => Classical.choice (cast (by sorry) (Nonempty.intro trivial)), fun _ => Classical.choice (cast (by sorry) (Nonempty.intro trivial))⟩) q
  sorry
