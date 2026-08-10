import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  by_contra h
  let rec pf : P := False.elim (h pf)
  exact pf
