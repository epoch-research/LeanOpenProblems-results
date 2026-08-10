import FormalConjectures.Util.ProblemImports
example : ∀ n : Nat, n = n := by
  classical
  decide
example (P : Prop) (h : P) : P := by
  classical
  decide
