import FormalConjectures.Util.ProblemImports
example : False := by
  let rec f : Nat → False
    | n+1 => f n
    | 0 => f 0
  exact f 0
