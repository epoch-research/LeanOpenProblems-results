import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A331343: $a(n) = \mathrm{lcm}(1,2,\dots,n) \cdot \sum_{k=1}^n \frac{2^{k-1} - 1}{k}$.

The expression is calculated in $\mathbb{N}$ using exact integer division property of the LCM.
$$a(n) = \sum_{k=1}^n \left(\frac{\mathrm{lcm}(1, \dots, n)}{k}\right) \cdot (2^{k-1} - 1)$$
-/
def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

-- Use the provided definition name `a` for the sequence.
def a (n : ℕ) : ℕ := A331343 n

-- The example theorems are removed as they were placeholders and are not part of the request.


/--
oeis_331343_conjecture_0: Conjecture: for n > 3, if n^3 | a(n), then n is prime.
If so, there are no such pseudoprimes.
-/
theorem oeis_331343_conjecture_0 : ∀ n : ℕ, n > 3 → n ^ 3 ∣ (a n) → Nat.Prime n := by
  intro n hn hd
  sorry
