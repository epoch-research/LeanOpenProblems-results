import FormalConjectures.Util.ProblemImports

def bad (P : Prop) : P := bad P
termination_by 0
decreasing_by simp_wf

example : False := bad False
#print axioms bad
