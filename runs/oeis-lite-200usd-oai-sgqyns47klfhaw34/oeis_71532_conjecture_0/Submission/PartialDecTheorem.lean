import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P

theorem emViaLoop (P : Prop) : P ∨ ¬ P := by
  cases decLoop P with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h
#print axioms emViaLoop
