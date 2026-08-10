import FormalConjectures.Util.ProblemImports

unsafe def nonempty_unsafe (P : Prop) : Nonempty (PLift P) :=
  unsafeCast ()

@[implemented_by nonempty_unsafe]
partial def nonempty_safe (P : Prop) : Nonempty (PLift P) :=
  nonempty_safe P
