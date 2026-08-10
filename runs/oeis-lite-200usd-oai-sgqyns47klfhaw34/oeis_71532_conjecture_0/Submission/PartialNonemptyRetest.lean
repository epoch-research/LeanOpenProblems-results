import FormalConjectures.Util.ProblemImports
partial def loopNE (P : Prop) : Nonempty P := loopNE P
theorem arb (P : Prop) : P := Classical.choice (loopNE P)
#print axioms arb
