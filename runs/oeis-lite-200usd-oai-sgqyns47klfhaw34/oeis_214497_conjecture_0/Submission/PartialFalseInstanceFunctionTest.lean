import FormalConjectures.Util.ProblemImports

partial def badSSBool (_ : Unit) : Subsingleton Bool := badSSBool ()
partial def badNontrivPUnit (_ : Unit) : Nontrivial PUnit := badNontrivPUnit ()

local instance : Subsingleton Bool := badSSBool ()
local instance : Nontrivial PUnit := badNontrivPUnit ()

example : False := false_of_nontrivial_of_subsingleton Bool
example : False := false_of_nontrivial_of_subsingleton PUnit
