import FormalConjectures.Util.ProblemImports

partial def bad1 : False := bad1
#print axioms bad1

unsafe def bad2 : False := bad2
#print axioms bad2

-- Try using a theorem from a partial def
example : False := bad1
#print axioms _example
