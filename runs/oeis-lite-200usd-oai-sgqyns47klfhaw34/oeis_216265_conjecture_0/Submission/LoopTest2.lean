import FormalConjectures.Util.ProblemImports

partial def badFalse2 (n : Nat) : False := badFalse2 n

theorem testFalse2 : False := badFalse2 0
#print axioms testFalse2
