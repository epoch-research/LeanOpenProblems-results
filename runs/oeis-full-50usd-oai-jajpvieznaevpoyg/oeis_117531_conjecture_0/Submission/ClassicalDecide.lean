import FormalConjectures.Util.ProblemImports
example (P : Prop) [Decidable P] (h : P) : P := by decide
example (P : Prop) (h : P) : P := by classical exact h
-- example (P : Prop) : P := by classical decide
