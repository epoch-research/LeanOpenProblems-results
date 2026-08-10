import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A215926: Smallest deficient number $k$ such that the product $k \cdot n$ is non-deficient (perfect or abundant).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sigma1(m) is defined as m.divisors.sum id
  let sigma1 (m : ℕ) : ℕ := m.divisors.sum id
  -- We define the set of candidate k values and take its infimum (which is the minimum element).
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}

/--
Conjecture: a(n) is 1, 3, or a power of 2.
This is OEIS A215926 Conjecture 1.
Note: The sequence is listed for n >= 2.
-/
theorem oeis_215926_conjecture_0 (n : ℕ) (hn : 2 ≤ n) : a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by sorry
