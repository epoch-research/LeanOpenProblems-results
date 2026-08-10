import FormalConjectures.Util.ProblemImports
#print Fact
#check Fact.out
#check Fact.mk
#synth Subsingleton (Fact False)
#synth Inhabited (Fact True)
#synth Inhabited (Fact False)
#check Classical.choice (α := Fact False)
#print axioms Fact.out
