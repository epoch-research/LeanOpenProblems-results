import FormalConjectures.Util.ProblemImports

open Nat

lemma mod_eq (p0 p1 p2 : ℕ) (h1 : p0 ≤ p1) (h2 : p1 ≤ p2) :
  (p0 * p1) % p2 = ((p2 - p1) * (p2 - p0)) % p2 := by
  have H : (p2 - p1) * (p2 - p0) = p2 * p2 - p2 * p0 - p1 * p2 + p1 * p0 := by sorry
  sorry
