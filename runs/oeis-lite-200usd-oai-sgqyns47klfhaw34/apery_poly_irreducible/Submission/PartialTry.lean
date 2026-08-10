import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k
partial def badProof (n : Nat) (hn : 1 ≤ n) : Irreducible (apery_poly n) := badProof n hn
example (n : Nat) (hn : 1 ≤ n) : Irreducible (apery_poly n) := badProof n hn
#print axioms badProof
