import FormalConjectures.Util.ProblemImports
partial def inhPos (n : Nat) : Inhabited (n + 1 > 0) := inhPos n
#check inhPos
#print axioms inhPos
