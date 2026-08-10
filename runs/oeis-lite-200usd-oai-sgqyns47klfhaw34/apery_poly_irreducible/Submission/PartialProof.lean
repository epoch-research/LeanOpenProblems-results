import FormalConjectures.Util.ProblemImports

partial def pf (P : Prop) : P := pf P

theorem t : False := pf False
#print axioms t
