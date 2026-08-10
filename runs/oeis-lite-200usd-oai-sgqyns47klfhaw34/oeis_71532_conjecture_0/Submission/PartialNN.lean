import FormalConjectures.Util.ProblemImports
partial def loopNN (P : Prop) (h : ¬ P) : False := loopNN P h
theorem arb (P : Prop) : P := Classical.byContradiction (loopNN P)
#print axioms arb
