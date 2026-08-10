import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  classical
  decide +revert
