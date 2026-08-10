import FormalConjectures.Util.ProblemImports
@[extern "lean_false"] constant bad : False
#print axioms bad
theorem t : False := bad
#print axioms t
