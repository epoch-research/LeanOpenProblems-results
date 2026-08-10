import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  classical
  let hp : P := Decidable.byContradiction (fun hn : ¬ P => hn hp)
  exact hp

def arbitrary (P : Prop) : P := by
  classical
  exact Decidable.byContradiction (fun hn : ¬ P => hn (arbitrary P))

#print axioms arbitrary
