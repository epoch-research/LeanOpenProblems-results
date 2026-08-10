import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
#print decLoop
#print axioms decLoop
#check decLoop.eq_def
#print decLoop.eq_def
#check decLoop._unary
#check decLoop.match_1
#eval (Lean.Name.mkSimple "x")
