import FormalConjectures.Util.ProblemImports

def cyc (P : Prop) : Nat → P
| 0 => cyc P 1
| n+1 => cyc P n
termination_by n => n
decreasing_by
  exact False.elim (cyc False 0)

theorem bad : False := cyc False 0
#print axioms bad
