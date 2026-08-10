import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  exact this

theorem bad (P : Prop) : P := by
  exact bad P
