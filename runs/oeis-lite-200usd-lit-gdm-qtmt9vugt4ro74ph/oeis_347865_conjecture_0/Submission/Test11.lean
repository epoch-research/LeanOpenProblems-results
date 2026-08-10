import FormalConjectures.Util.ProblemImports

partial def my_partial_cast {A B : Type} [Nonempty B] (x : A) : B :=
  unsafeCast x
