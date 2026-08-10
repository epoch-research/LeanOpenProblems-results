import FormalConjectures.Util.ProblemImports

inductive BadP : Prop
| mk : (BadP → False) → BadP

def badp_not : BadP → False
| BadP.mk f => f (BadP.mk f)

theorem t : False := badp_not (BadP.mk badp_not)
#print axioms t
