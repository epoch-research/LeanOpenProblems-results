import FormalConjectures.Util.ProblemImports

axiom hiddenFalse : False
opaque opaqueFalse : False := hiddenFalse

theorem badFalse : False := opaqueFalse
#print axioms badFalse
#print axioms opaqueFalse
