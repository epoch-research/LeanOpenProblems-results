import FormalConjectures.Util.ProblemImports
variable (P : Prop)
#synth Subsingleton (Decidable P)
partial def loopDec (P : Prop) : Decidable P := loopDec P
example (h : loopDec P = Decidable.isTrue (by exact (Classical.choice ?_) : P)) : P := by sorry
#print Decidable.isTrue.injEq
#print Decidable.isFalse.injEq
#check @Subsingleton.elim (Decidable P) _ (loopDec P)
