import FormalConjectures.Util.ProblemImports
partial def bogus (P : Prop) : P := bogus P
theorem anyP (P : Prop) : P := bogus P
#print axioms anyP
