import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P
#check loopDec.eq_def
#check loopDec._unary
#print loopDec.eq_def
