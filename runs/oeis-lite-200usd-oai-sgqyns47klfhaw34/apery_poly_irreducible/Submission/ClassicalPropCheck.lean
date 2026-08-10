import FormalConjectures.Util.ProblemImports
#check Classical.choice
#check Classical.decEq
#check Classical.propComplete
#check propComplete
#check Classical.choice (p := Nonempty False)
example (P : Prop) : Decidable P := Classical.propDecidable P
-- #check (Classical.choice (show Nonempty P from ?_))
