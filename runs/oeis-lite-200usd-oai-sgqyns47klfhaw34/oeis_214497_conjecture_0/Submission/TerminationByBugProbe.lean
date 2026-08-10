import FormalConjectures.Util.ProblemImports

-- Should fail: recursive call does not decrease.
def badRecProof (n : ℕ) : False := badRecProof n
termination_by n
decreasing_by omega

example : False := badRecProof 0
#print axioms badRecProof
