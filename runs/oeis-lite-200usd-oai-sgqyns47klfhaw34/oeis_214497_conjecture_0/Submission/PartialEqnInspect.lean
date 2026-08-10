import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P
#print loopDec
#check loopDec.eq_1
#check loopDec._unary
#print axioms loopDec
