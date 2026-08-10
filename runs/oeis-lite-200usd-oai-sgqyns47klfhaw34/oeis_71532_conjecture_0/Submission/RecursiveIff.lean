import FormalConjectures.Util.ProblemImports
axiom P : Prop

noncomputable def iffPTrue : P ↔ True where
  mp := fun _ => trivial
  mpr := fun _ => Eq.mp (propext iffPTrue).symm trivial

#print axioms iffPTrue
example : P := iffPTrue.mpr trivial
#print axioms _example
