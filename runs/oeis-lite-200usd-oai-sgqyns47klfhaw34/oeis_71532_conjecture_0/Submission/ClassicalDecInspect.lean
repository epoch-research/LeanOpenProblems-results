import FormalConjectures.Util.ProblemImports
#check Classical.propDecidable
#print Classical.propDecidable
#check (Classical.propDecidable (p := False))
#check (Classical.choice (show Nonempty (Decidable False) from ⟨Classical.propDecidable⟩))
