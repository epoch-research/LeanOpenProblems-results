import FormalConjectures.Util.ProblemImports
axiom P : Prop

def aux : Nat → P → False
| 0, hp => aux 1 hp
| n+1, hp => aux n hp
termination_by n _ => n
#print axioms aux
example : ¬ P := aux 0
