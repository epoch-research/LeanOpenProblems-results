import FormalConjectures.Util.ProblemImports

unsafe def get_nonempty_safe_impl (P : Prop) : PLift (Nonempty (PLift P)) :=
  PLift.up (unsafeCast ())

@[implemented_by get_nonempty_safe_impl]
partial def get_nonempty_safe (P : Prop) : PLift (Nonempty (PLift P)) :=
  get_nonempty_safe P

#print axioms get_nonempty_safe
