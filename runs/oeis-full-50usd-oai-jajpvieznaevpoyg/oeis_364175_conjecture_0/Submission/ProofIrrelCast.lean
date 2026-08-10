import FormalConjectures.Util.ProblemImports
example (P Q : Prop) (hp : P) : Q := by
  have hheq : hp ≍ (Classical.choice (show Nonempty Q from ?_)) := proof_irrel_heq hp _
  · exact ?_
  · exact ?_
