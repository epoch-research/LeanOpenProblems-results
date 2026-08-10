import FormalConjectures.Util.ProblemImports

instance badNontrivialPUnit : Nontrivial PUnit := badNontrivialPUnit

example : False := false_of_nontrivial_of_subsingleton PUnit

#print axioms badNontrivialPUnit
#print axioms this
