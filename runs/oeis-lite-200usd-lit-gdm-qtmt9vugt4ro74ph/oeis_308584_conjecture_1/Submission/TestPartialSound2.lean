import FormalConjectures.Util.ProblemImports

partial def bad_proof (n : Nat) (h : Inhabited False) : False :=
  bad_proof n h

theorem bad_proof_eq (n : Nat) (h : Inhabited False) : False :=
  bad_proof n h

#print axioms bad_proof_eq
