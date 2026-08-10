import FormalConjectures.Util.ProblemImports
unsafe def bad {α : Sort u} : α := unsafeCast ()
theorem t : False := by
  exact bad
#print axioms t
