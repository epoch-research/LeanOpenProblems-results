import FormalConjectures.Util.ProblemImports

open Nat

/--
A349246: Number of ways to write $n$ as $w^8 + x^4 + 2y^4 + 4z^4 + t(t+1)$, where $w, x, y, z$, and $t$ are nonnegative integers.
-/
def A349246 (n : ℕ) : ℕ :=
  let B := Finset.range (n + 1)
  Finset.sum B $ fun w =>
  Finset.sum B $ fun x =>
  Finset.sum B $ fun y =>
  Finset.sum B $ fun z =>
  Finset.sum B $ fun t =>
    if w^8 + x^4 + 2 * y^4 + 4 * z^4 + t * (t + 1) = n then 1 else 0

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... -/
theorem oeis_349246_conjecture_0 (n : ℕ) : A349246 n > 0 := by
  sorry
