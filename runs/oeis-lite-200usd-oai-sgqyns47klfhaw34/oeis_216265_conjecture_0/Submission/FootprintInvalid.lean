import FormalConjectures.Util.ProblemImports

example : False := by
  exact answer(sorry)
#print axioms FootprintInvalid._example_1

unsafe def badFalse : False := unsafeCast ()
-- cannot use unsafe in safe theorem directly maybe
#print axioms badFalse

axiom myAx : False
#print axioms myAx
