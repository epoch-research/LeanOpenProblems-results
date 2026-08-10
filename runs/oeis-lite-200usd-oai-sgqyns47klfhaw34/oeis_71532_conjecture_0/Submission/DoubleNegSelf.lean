import FormalConjectures.Util.ProblemImports
axiom P : Prop

def nn : ¬¬P := fun hn => hn (Classical.byContradiction nn)
#print axioms nn

theorem p : P := Classical.byContradiction nn
#print axioms p
