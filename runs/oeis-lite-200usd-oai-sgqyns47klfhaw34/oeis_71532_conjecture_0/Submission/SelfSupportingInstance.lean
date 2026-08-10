import FormalConjectures.Util.ProblemImports

class BadClass : Prop where h : False

theorem noBad [BadClass] : False := BadClass.h

instance badInst : BadClass := ⟨noBad⟩

theorem badFalse : False := noBad
#print axioms badFalse
