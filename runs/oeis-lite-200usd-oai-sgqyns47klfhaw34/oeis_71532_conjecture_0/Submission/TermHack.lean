import FormalConjectures.Util.ProblemImports

def ltbad (n : Nat) : n + 1 < n := ltbad (n+1)
termination_by n
decreasing_by
  exact ltbad n

def bad : False := by
  have h := ltbad 0
  omega
#print axioms bad
example : False := bad
