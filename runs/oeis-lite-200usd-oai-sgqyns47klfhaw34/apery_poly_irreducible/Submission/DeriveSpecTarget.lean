import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

deriving instance Nonempty for (Irreducible (apery_poly 2))
example : Irreducible (apery_poly 2) := Classical.choice inferInstance
#print axioms instNonemptyIrreducible
