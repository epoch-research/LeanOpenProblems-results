import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P
#print axioms decLoop
#print decLoop
#check decLoop


example (P : Prop) : P ∨ ¬ P := by
  cases decLoop P with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

example (P : Prop) : P := by
  cases decLoop P with
  | isTrue h => exact h
  | isFalse h =>
      -- stuck
      sorry
