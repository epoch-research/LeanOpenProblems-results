import FormalConjectures.Util.ProblemImports

unsafe def my_inhabited_impl (P : Prop) : Inhabited (PLift P) :=
  ⟨unsafeCast ()⟩

@[implemented_by my_inhabited_impl]
partial def my_inhabited (P : Prop) : Inhabited (PLift P) :=
  my_inhabited P

#print axioms my_inhabited
