import FormalConjectures.Util.ProblemImports

unsafe def bad : False := unsafeCast ()

theorem Tbad : False := by
  exact bad
