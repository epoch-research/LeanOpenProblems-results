import FormalConjectures.Util.ProblemImports

partial def exFalse (_ : Unit) : ∃ n : Nat, False := exFalse ()
#print axioms exFalse
example : False := (exFalse ()).2
