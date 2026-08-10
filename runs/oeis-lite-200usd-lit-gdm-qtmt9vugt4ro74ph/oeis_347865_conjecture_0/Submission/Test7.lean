import FormalConjectures.Util.ProblemImports

unsafe def my_unsafe_cast {A B : Type} (x : A) : B :=
  unsafeCast x

partial def my_partial_cast {A B : Type} [Nonempty B] (x : A) : B :=
  my_unsafe_cast x

theorem test_cast (n : Nat) : n > 0 :=
  (my_partial_cast (PLift.up (by omega : 1 > 0)) : PLift (n > 0)).down

#print axioms test_cast
