import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P
#print loopDec
#print axioms loopDec
#check loopDec
example (P:Prop) : Decidable P := loopDec P
-- compare with classical?
example (P:Prop) : Nonempty (Decidable P) := ⟨loopDec P⟩
