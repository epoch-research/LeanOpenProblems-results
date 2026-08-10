import FormalConjectures.Util.ProblemImports
partial def loopNat : Nat := loopNat
partial def loopDec (P : Prop) : Decidable P := loopDec P
#check loopNat
#print axioms loopNat
#print axioms loopDec
example : Nat := loopNat
