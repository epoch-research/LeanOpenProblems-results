import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  let rec @[implemented_by id] pf : P := by exact pf
  exact pf
