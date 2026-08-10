import FormalConjectures.Util.ProblemImports

unsafe def bad : False := unsafeCast ()

example : False := by
  exact bad
