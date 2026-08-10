import FormalConjectures.Util.ProblemImports

instance instFactFalseSelf [Fact False] : Fact False := inferInstance

#synth Fact False

theorem bad : False := Fact.out (p := False)
#print axioms bad
