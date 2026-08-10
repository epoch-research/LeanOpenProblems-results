import FormalConjectures.Util.ProblemImports
#check Quot.sound
#check Quot.exact
#check Quot.ind
#check Quot.lift

universe u
example (P : Prop) : P := by
  let R : Prop → Prop → Prop := fun A B => A → B
  let q : Prop → Quot R := fun A => Quot.mk R A
  have h1 : q P = q True := Quot.sound (fun hp => True.intro)
  have h2 : q True = q P := h1.symm
  have imp : True → P := Quot.exact h2
  exact imp True.intro

#print axioms _example
