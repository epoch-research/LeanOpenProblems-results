import FormalConjectures.Util.ProblemImports
axiom P : Prop
#check (inferInstance : Inhabited (Decidable P))
#print instInhabitedDecidable
