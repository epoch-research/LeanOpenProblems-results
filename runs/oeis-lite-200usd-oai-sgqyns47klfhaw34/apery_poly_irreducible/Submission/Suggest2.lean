import FormalConjectures.Util.ProblemImports
open Nat Polynomial

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

set_option maxHeartbeats 1000000
example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  apply?
