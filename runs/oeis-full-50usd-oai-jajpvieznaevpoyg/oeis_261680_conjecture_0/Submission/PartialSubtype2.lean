import FormalConjectures.Util.ProblemImports
partial def pickEven (_ : Unit) : {n : Nat // n % 2 = 0} := pickEven ()
#print axioms pickEven
theorem t : ((pickEven ()).1 % 2 = 0) := (pickEven ()).2
#print axioms t
