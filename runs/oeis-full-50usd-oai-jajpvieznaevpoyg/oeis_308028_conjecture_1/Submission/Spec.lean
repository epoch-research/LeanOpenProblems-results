import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A308028: Number of ways to write $2n+1$ as $p + q + r$ with $2p + 4q + 6r$ a square, where $p,q,r$ are odd primes.
-/
def A308028 (n : ℕ) : ℕ :=
  let N := 2 * n + 1

  -- Summation over all possible natural numbers p and q up to N.
  (range (N + 1)).sum fun p =>
    (range (N + 1)).sum fun q =>
      -- Check if p + q leaves a positive remainder r.
      if p + q < N then
        let r := N - p - q
        let C := 2 * p + 4 * q + 6 * r

        -- Check all conditions: p, q, r are odd primes AND 2p+4q+6r is a square.
        if (p.Prime ∧ p ≠ 2) ∧
           (q.Prime ∧ q ≠ 2) ∧
           (r.Prime ∧ r ≠ 2) ∧
           (C.sqrt * C.sqrt = C)
        then 1 else 0
      else 0

/--
The 2-4-6 Conjecture: a(n) > 0 for all n > 6. In other words, any odd integer greater than 14 can be written as the sum of three odd primes p,q,r for which 2*p + 4*q + 6*r is an integer square.
-/
theorem oeis_308028_conjecture_1 : ∀ (n : ℕ), 6 < n → 0 < A308028 n :=
by sorry
