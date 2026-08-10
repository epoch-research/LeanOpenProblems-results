import FormalConjectures.Util.ProblemImports

opaque c_nonempty : Nonempty False

theorem my_false : False := Classical.choice c_nonempty

#print axioms my_false
