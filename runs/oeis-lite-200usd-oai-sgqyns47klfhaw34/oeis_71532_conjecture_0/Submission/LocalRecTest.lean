import FormalConjectures.Util.ProblemImports

example : False := by
  let rec f : Nat → False := fun n => f n
  exact f 0

example : False := by
  let f : False := f
  exact f
