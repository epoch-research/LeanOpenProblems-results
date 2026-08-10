import FormalConjectures.Util.ProblemImports

opaque my_panic (P : Prop) : P

theorem test_opaque : False := my_panic False

#print axioms test_opaque
