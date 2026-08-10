import FormalConjectures.Util.ProblemImports
partial def erasedLoop (P : Prop) : Erased P := erasedLoop P
example : False := Erased.out_proof (erasedLoop False)
#print axioms erasedLoop
#print axioms _example
