import FormalConjectures.Util.ProblemImports

partial def badSSBool : Subsingleton Bool := badSSBool
partial def badNontrivPUnit : Nontrivial PUnit := badNontrivPUnit

example : False := false_of_nontrivial_of_subsingleton Bool
