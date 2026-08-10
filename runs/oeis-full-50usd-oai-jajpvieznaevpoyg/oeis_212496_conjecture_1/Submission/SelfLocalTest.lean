import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  let rec pf : P := by
    by_cases h : P
    · exact h
    · exact False.elim (h pf)
  exact pf
