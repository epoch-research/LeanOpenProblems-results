import FormalConjectures.Util.ProblemImports
#check Classical.propComplete
#print Classical.propComplete
#print axioms Classical.propComplete

example (P : Prop) : P ∨ ¬ P := by
  rcases Classical.propComplete P with h | h
  · left
    rw [h]
    trivial
  · right
    rw [h]
    intro hf; exact hf

example (P : Prop) : ¬ P ∨ P := by
  exact (Classical.em P).symm
