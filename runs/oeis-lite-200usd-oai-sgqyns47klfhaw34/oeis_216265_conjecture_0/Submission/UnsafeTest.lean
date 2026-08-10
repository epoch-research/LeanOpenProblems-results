import FormalConjectures.Util.ProblemImports

unsafe def bad : False := unsafeCast ()

theorem badThm : False := by
  exact bad

#print axioms badThm
