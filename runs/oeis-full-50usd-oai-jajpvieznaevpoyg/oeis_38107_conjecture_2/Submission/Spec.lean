import FormalConjectures.Util.ProblemImports

open Nat

/--
A038107: Number of primes $< n^2$.
This is the cardinality of the set of primes strictly less than $n^2$.
-/
def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

/--
Conjecture: All the numbers Sum_{i=j,...,k} 1/a(i) with 1 < j <= k have pairwise distinct fractional parts.
-/
theorem oeis_38107_conjecture_2 :
  -- Define the reciprocal function, coercing A038107 i to a real number.
  let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
  -- Iterate over two pairs of indices (j, k) and (j', k')
  ∀ j k j' k' : ℕ,
    -- Constraints 1 < j <= k
    1 < j → j ≤ k →
    -- Constraints 1 < j' <= k'
    1 < j' → j' ≤ k' →
    -- If their fractional parts are equal...
    Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
    -- ...then the index pairs must be identical.
    (j, k) = (j', k') := by sorry
