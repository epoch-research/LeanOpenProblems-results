import FormalConjectures.Util.ProblemImports

example : False := by
  let rec go : False := go
  exact go

example (P : Prop) : P := by
  let rec go : P := go
  exact go
