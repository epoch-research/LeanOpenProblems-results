import FormalConjectures.Util.ProblemImports
partial def loopNat : Nat := loopNat
partial def loopDec (P : Prop) : Decidable P := loopDec P
#print loopNat
#print loopDec
#check loopNat.eq_def
#check loopDec.eq_def
#check loopNat._unary
#check loopNat._unsafe_rec
#reduce loopNat
#print axioms loopNat
#print axioms loopDec
