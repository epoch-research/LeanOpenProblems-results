import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast ()
example : True := (fun (_ : False) => trivial) bad
#print axioms _example
example : True := by
  exact (fun (_ : False) => trivial) bad
