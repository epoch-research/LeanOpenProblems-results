import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k
#synth Decidable (Irreducible (apery_poly 3))
#synth Decidable (Irreducible (apery_poly n))
example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  native_decide
