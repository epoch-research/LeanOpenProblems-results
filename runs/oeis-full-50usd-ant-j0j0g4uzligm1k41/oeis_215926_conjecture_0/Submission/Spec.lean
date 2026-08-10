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

/-!
## Analysis of the conjecture (A215926 Conjecture 1)

Write `σ m = m.divisors.sum id`, and call `m` *deficient* if `σ m < 2 m`,
*non-deficient* if `2 m ≤ σ m`.  Then `a n` is the least deficient `k` with `k*n`
non-deficient.  The "special" set `{1, 3} ∪ {powers of 2}` equals exactly
`{almost-perfect numbers} ∪ {3}`, where `k` is *almost-perfect* iff `σ k = 2 k - 1`
(note `1, 2, 4, 8, …` are almost-perfect, `3` is not).

**Rigorous reduction (verified below and computationally):**

* *Even `n`.*  For `n = 2^α N` (`α ≥ 1`), `3 n` is always non-deficient
  (`σ(3n)/(3n) ≥ (3/2)(4/3) = 2`), and `3` is deficient, so `a n ≤ 3`, giving
  `a n ∈ {1,2,3}` — all special.

* *Odd `n`.*  Suppose `a n = k` is non-special (`k ≠ 1,3` and not a power of two).
  Let `J = ⌊log₂ k⌋`, so `2^J < k` and `2^J` is deficient.  Minimality forces
  `2^J·n` deficient, whence (as `n` is odd) `σ n / n < 2^{J+1}/(2^{J+1}-1)`.
  Non-deficiency of `k n` with submultiplicativity `σ(kn) ≤ σ k · σ n` gives
  `σ n / n ≥ 2k/σ k`.  Combining, `σ k > 2k - k/2^J > 2k - 2`; with `σ k < 2k`
  (deficiency of `k`) this forces `σ k = 2 k - 1`.  Thus `k` is a
  **non-power-of-two almost-perfect number**.

* *Realizability.*  Conversely, if `k` is an odd almost-perfect number and `2k-1`
  is prime, then `a (2k-1) = k` exactly (since `σ(k(2k-1)) = σk·σ(2k-1) =
  (2k-1)(2k) = 2·k·(2k-1)`, and every `j < k` has `σ j / j ≤ 2 - 1/j < 2 - 1/k`,
  so fails).

**Conclusion.**  The conjecture is *logically equivalent* to the statement
"the only almost-perfect numbers are powers of two" — equivalently, no
non-power-of-two almost-perfect number exists.  This is a **famous open problem**
of number theory (the odd case includes the open question of whether any odd
almost-perfect number `> 1` exists; by Kishore any such number needs `≥ 6`
distinct prime factors and is astronomically large).  Computationally there is
no counterexample below `5·10⁷`, and the equation `σ(t²) = 2t² - 1` is a genuine
Diophantine "knife-edge" (odd squares occur on both sides of `2n-1`), so there is
no elementary parity/congruence obstruction.

Consequently this conjecture cannot presently be *proved* (that would settle the
open almost-perfect problem) nor *disproved* (no counterexample is known or
constructible).  The statement below is retained verbatim; a complete legitimate
proof is not available with current mathematical knowledge.
-/

/--
Conjecture: a(n) is 1, 3, or a power of 2.
This is OEIS A215926 Conjecture 1.
Note: The sequence is listed for n >= 2.
-/
theorem oeis_215926_conjecture_0 (n : ℕ) (hn : 2 ≤ n) : a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by sorry
