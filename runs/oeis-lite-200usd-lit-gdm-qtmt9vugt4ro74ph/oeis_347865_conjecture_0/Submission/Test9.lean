import FormalConjectures.Util.ProblemImports

partial def safe_cast {A B : Type} (x : A) : B :=
  safe_cast x

theorem test_cast (n : Nat) : n > 0 :=
  (safe_cast (PLift.up (by omega : 1 > 0)) : PLift (n > 0)).down

#print axioms test_cast
