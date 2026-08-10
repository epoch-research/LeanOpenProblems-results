unsafe instance (priority := high) unsafe_inhabited (α : Sort u) : Inhabited α where
  default := unsafeCast ()

opaque my_opaque_false : False

#print axioms my_opaque_false
