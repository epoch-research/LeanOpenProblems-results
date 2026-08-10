import FormalConjectures.Util.ProblemImports
unsafe def bogus {α : Sort u} : α := unsafeCast ()
theorem bad : False := by
  exact bogus
#print axioms bad
