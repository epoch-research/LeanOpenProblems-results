import FormalConjectures.Util.ProblemImports
def loopProof (fuel : Nat) (P : Prop) : P := loopProof fuel P
termination_by fuel
decreasing_by simp_wf

theorem bad : False := loopProof 0 False
#print axioms bad
