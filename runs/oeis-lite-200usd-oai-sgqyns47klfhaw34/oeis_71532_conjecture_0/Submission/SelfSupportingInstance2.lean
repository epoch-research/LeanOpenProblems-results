import FormalConjectures.Util.ProblemImports

class BadClass2 : Prop where h : False

theorem noBad2 [BadClass2] : False := BadClass2.h

instance badInst2 : BadClass2 := ⟨@noBad2 badInst2⟩

theorem badFalse2 : False := noBad2
#print axioms badFalse2
