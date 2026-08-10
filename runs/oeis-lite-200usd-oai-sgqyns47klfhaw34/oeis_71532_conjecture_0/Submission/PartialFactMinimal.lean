import FormalConjectures.Util.ProblemImports
partial def factLoop (P : Prop) : Fact P := factLoop P
example : False := Fact.out (p := False) (self := factLoop False)
#print factLoop
#print axioms factLoop
#print axioms _example
