import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma h_sum_mod_test (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ)^5 ∣ 4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) + 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3) := by
  aesop

