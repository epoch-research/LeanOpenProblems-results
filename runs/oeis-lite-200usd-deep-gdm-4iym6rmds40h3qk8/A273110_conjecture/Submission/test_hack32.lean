import FormalConjectures.Util.ProblemImports

unsafe instance (priority := high) unsafe_inhabited (α : Sort u) : Inhabited α where
  default := unsafeCast ()

-- Can we use this unsafe instance to define an opaque definition?
opaque my_opaque_false : False

#print axioms my_opaque_false
