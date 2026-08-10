import FormalConjectures.Util.ProblemImports

partial def badNontrivialPUnit : Nontrivial PUnit := badNontrivialPUnit
attribute [instance] badNontrivialPUnit

example : False := false_of_nontrivial_of_subsingleton PUnit

#print axioms badNontrivialPUnit
#print axioms _example
