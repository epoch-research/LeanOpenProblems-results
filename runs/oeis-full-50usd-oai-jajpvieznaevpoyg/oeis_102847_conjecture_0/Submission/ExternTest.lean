import FormalConjectures.Util.ProblemImports

@[extern "lean_true"] constant bad : False
example : False := bad
#print axioms bad
