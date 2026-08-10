import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A196697: Number of primes of the form of $2^n \pm 2^k \pm 1$ with $0 \le k < n$.
-/
def a (n : ℕ) : ℕ :=
  let candidates_set : Finset ℕ :=
    (range n).biUnion fun k =>
      let p2n := 2^n
      let p2k := 2^k
      -- The four forms are $2^n \pm 2^k \pm 1$ and the negative sign is part of the constant
      insert (p2n + p2k + 1) $ insert (p2n + p2k - 1) $
      insert (p2n - p2k + 1) $ {p2n - p2k - 1}

  -- Filter the set of distinct candidates for primality and return the cardinality.
  (candidates_set.filter Nat.Prime).card

/-- Conjecture: all terms of this sequence are greater than 0. -/
theorem oeis_196697_conjecture_0 :
  ∀ n : ℕ, 1 ≤ n → a n > 0 :=
by sorry
