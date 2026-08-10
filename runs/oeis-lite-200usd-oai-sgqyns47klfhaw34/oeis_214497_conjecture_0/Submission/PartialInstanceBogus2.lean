import FormalConjectures.Util.ProblemImports

partial def badNontrivialPUnit (u : Unit) : Nontrivial PUnit := badNontrivialPUnit u
instance : Nontrivial PUnit := badNontrivialPUnit ()

example : False := false_of_nontrivial_of_subsingleton PUnit

#print axioms badNontrivialPUnit
#print axioms _example
