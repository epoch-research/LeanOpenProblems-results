import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n -- dummy

partial def get_proof_opt (n : Nat) : Option (PLift (a n > 0)) :=
  get_proof_opt n

theorem test_thm (n : Nat) : Option (PLift (a n > 0)) :=
  get_proof_opt n

#print axioms test_thm
