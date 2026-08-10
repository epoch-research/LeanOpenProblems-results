import FormalConjectures.Util.ProblemImports

example {P : Prop} (hp : P) (hn : ¬ P) : (Decidable.isTrue hp : Decidable P) ≠ Decidable.isFalse hn := by
  intro h
  cases h

#check Decidable.noConfusion
#print Decidable.noConfusion
