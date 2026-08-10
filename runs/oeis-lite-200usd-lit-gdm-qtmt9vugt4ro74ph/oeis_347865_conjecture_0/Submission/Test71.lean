import FormalConjectures.Util.ProblemImports

unsafe def cast_impl {A B : Type} (h : Nonempty B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} (h : Nonempty B) (x : A) : B :=
  safe_cast h x
