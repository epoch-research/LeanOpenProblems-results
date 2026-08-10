import FormalConjectures.Util.ProblemImports

def goodImpl (_ : Unit) : Bool := true
@[implemented_by goodImpl] def badBoolImpl (_ : Unit) : Bool := false
#eval badBoolImpl ()
theorem badThm : badBoolImpl () = true := by
  native_decide
#print axioms badThm
#print badThm
