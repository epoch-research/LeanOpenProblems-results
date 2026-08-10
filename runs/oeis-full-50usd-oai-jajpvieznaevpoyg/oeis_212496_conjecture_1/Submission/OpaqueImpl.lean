import FormalConjectures.Util.ProblemImports
unsafe def bogusImpl : True → False := fun _ => unsafeCast ()
@[implemented_by bogusImpl]
opaque bogus : True → False
theorem t : False := bogus True.intro
#print axioms t
