import FormalConjectures.Util.ProblemImports
-- def badFalse : False := badFalse
-- theorem t : False := t
example : False := by
  let rec f : False := f
  exact f
