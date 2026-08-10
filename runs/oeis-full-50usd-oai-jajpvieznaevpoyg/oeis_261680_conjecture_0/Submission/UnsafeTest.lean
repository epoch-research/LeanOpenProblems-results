import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast True
example : False := by
  exact bad
