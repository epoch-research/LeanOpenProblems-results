import FormalConjectures.Util.ProblemImports
#check (inferInstance : Fintype Prop)
#check (inferInstance : DecidableEq Prop)
#check (inferInstance : Fintype (Set Prop))
#eval Fintype.card (Set Prop)
#eval Fintype.card (Prop → Prop)
#eval Fintype.card Prop
#print axioms Prop.fintype
#print axioms instFintypeSet
