import FormalConjectures.Util.ProblemImports
axiom P : Prop

def bad (n : Nat) : P := bad (n+1)
termination_by n => n
decreasing_by
  have hp : P := bad 0
  exact False.elim (by
    -- cannot get false from P
    admit)
#print axioms bad
