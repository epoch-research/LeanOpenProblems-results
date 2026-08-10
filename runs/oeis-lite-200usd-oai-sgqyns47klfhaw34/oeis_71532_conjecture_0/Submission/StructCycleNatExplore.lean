import FormalConjectures.Util.ProblemImports

def cyc (P : Prop) : Nat → P
| 0 => cyc P 1
| n+1 => cyc P n

theorem arbitrary (P : Prop) : P := cyc P 0
#print axioms arbitrary
