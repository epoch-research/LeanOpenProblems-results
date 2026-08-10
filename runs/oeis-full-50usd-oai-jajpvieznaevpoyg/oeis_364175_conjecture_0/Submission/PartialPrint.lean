import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
#print decLoop
#print decLoop._unsafe_rec
#print axioms decLoop
#check decLoop.eq_1
#check decLoop.eq_def
