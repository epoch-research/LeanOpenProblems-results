import FormalConjectures.Util.ProblemImports

-- Direct recursive proposition-valued function

def v : Nat → Prop
| 0 => v 0 → False
| _+1 => True

#print axioms v
example : False := by
  have h1 : v 0 → False := by
    change (v 0 → False) → False
    intro h
    exact h h
  have h2 : (v 0 → False) := by
    change v 0
    exact h1
  exact h1 h2
