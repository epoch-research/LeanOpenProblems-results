import FormalConjectures.Util.ProblemImports

partial def loopNat (_ : Unit) : Nat := loopNat ()
#print loopNat
#check loopNat.eq_def
#check loopNat._unary
#check loopNat._unsafe_rec
