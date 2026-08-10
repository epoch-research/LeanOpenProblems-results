import FormalConjectures.Util.ProblemImports

example (n : ℕ) : n = 1 := by
  congr

example : (True : Prop) = False := by
  congr
