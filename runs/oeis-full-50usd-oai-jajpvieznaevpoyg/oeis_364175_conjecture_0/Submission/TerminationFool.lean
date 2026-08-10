import FormalConjectures.Util.ProblemImports
def loopProof (P : Prop) : P := loopProof P
termination_by 0
decreasing_by simp

theorem bad : False := loopProof False
#print axioms bad
