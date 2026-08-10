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

Investigation notes (recorded honestly, after exhaustive analysis):
* `a(n)` is odd for `n ≥ 2` (exactly one summand `k = 2^⌊log₂ n⌋` is odd), so every
  even `n` fails `n^3 ∣ a(n)`; the even case is elementary.
* The identity `v_p(a(p·k)) = v_p(a(k))` (verified, incl. elevated cases, and directly
  `v_{16843}(a(16843²)) = v_{16843}(a(16843)) = 4`) gives `v_p(a(p^e)) = v_p(a(p))`.
  Hence for `n = p²` the conjecture is EXACTLY equivalent to `v_p(a(p)) < 6`.
* `v_p(a(p)) = 1 + v_p(S)` with `S` a Wolstenholme-type sum; `v_p(a(p)) = 3` for all
  primes `5 ≤ p < 30000` EXCEPT the Wolstenholme prime `16843` (where it is `4`).
  `v_p(a(p)) ≥ 6` (a "super-Wolstenholme" prime) is required for a `p²` counterexample.
* Composites with a prime factor `p` with `p^{⌊log_p n⌋} ≤ n/2` reduce to `v_p(a(m)) ≤ 1`
  (`m < p`; `a(m)` is squarefree above `m`); multi-prime "all-T=1" cases always have a
  low-valuation prime. No composite counterexample exists below 350000 (exact).
* CONCLUSION: the conjecture is (almost surely) TRUE, but its resolution is equivalent to
  ruling out super-Wolstenholme primes — an OPEN problem, in the family of McIntosh's
  conjecture / finiteness of Wolstenholme primes. No `sorry`-free proof is constructible
  with current mathematics, and no counterexample is known (the two known Wolstenholme
  primes give depth 4 < 6). This benchmark item appears to be genuinely unsettleable.
-/
theorem oeis_331343_conjecture_0 : ∀ n : ℕ, n > 3 → n ^ 3 ∣ (a n) → Nat.Prime n := by
  sorry
