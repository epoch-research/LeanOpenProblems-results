import FormalConjectures.Util.ProblemImports

partial def bad_identity (n : Nat) : Nat :=
  bad_identity n

theorem bad_identity_eq (n : Nat) : bad_identity n = bad_identity n :=
  rfl

#print axioms bad_identity_eq
