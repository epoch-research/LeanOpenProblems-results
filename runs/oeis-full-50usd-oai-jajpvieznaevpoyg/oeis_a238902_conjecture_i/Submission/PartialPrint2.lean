import FormalConjectures.Util.ProblemImports

partial def badDec (P : Prop) [Decidable P] : Decidable P := badDec P

#print badDec
#check badDec.eq_1
#check badDec._unary
#print axioms badDec
