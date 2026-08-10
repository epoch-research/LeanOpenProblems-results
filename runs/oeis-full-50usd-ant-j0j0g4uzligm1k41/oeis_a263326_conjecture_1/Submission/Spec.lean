import FormalConjectures.Util.ProblemImports

open Nat Rat Finset

/--
A263326: Denominator of the rational number $\sum_{d|n} \frac{1}{d+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if hn : n > 0 then
    (Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + 1 : ℚ)⁻¹).den
  else 0

-- Definition of the generalized sum from the conjecture
/--
The generalized sum $\sum_{d|n} \frac{1}{(d+k)^s}$ for $n, k, s \in \mathbb{N}$.
We require $n>0$ for the set of divisors to be non-empty, and $k, s > 0$ from the conjecture's context.
Since $d \ge 1$ for $d \in \mathrm{divisors}(n)$ when $n>0$, the denominator $d+k$ is non-zero.
-/
noncomputable def sum_divisors_inv_pow (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast : ℚ)⁻¹ ^ s

/-!
## Disproof of the conjecture

The conjecture asserts that for *every* `k, s ≥ 1`, the numbers
`∑_{d|n} 1/(d+k)^s` (`n = 1, 2, 3, …`) have pairwise distinct fractional parts and
none of them is an integer.

While the original Shevelev conjecture (the case `k = 1`, `s = 1`) concerns a specific
sequence, the statement formalized here quantifies over **all** `k` and `s`, and the
injectivity ("pairwise distinct fractional parts") part **fails** already for `s = 1`.

A concrete counterexample is `k = 31`, `s = 1`:
* `1829 = 31 · 59`, so `divisors 1829 = {1, 31, 59, 1829}` and
  `f(1829) = 1/32 + 1/62 + 1/90 + 1/1860`;
* `divisors 5 = {1, 5}`, so `f(5) = 1/32 + 1/36`.

These two values are **exactly equal** (both `= 17/288`), because
`1/62 + 1/90 + 1/1860 = 1/36`.  Hence `f(5) = f(1829)` while `5 ≠ 1829`, so the two
sums have equal fractional parts even though they correspond to distinct `n`,
contradicting injectivity.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private lemma sum_divisors_inv_pow_five : sum_divisors_inv_pow 5 31 1 = 17 / 288 := by
  unfold sum_divisors_inv_pow
  have h : Nat.divisors 5 = {1, 5} := by decide
  rw [h]
  norm_num [Finset.sum_pair]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private lemma sum_divisors_inv_pow_1829 : sum_divisors_inv_pow 1829 31 1 = 17 / 288 := by
  unfold sum_divisors_inv_pow
  have h : Nat.divisors 1829 = {1, 31, 59, 1829} := by decide
  rw [h]
  norm_num [Finset.sum_insert, Finset.mem_insert]

/--
Disproof of the A263326 generalized conjecture: it is **false** that for all positive
integers `k` and `s` the numbers `∑_{d|n} 1/(d+k)^s` have pairwise distinct fractional
parts and are never integers.  Indeed, for `k = 31`, `s = 1` we have
`f(5) = f(1829) = 17/288` while `5 ≠ 1829`, violating injectivity of the fractional parts.
-/
theorem oeis_a263326_conjecture_1.disproof :
  ¬ (∀ (k s : ℕ), k > 0 ∧ s > 0 →
  (∀ n : ℕ, n > 0 →
    -- The value is not an integer
    (Int.fract (sum_divisors_inv_pow n k s) ≠ 0))
  ∧
  -- The fractional parts are distinct for distinct n
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → Int.fract (sum_divisors_inv_pow n₁ k s) = Int.fract (sum_divisors_inv_pow n₂ k s) → n₁ = n₂)) := by
  intro h
  obtain ⟨_, hinj⟩ := h 31 1 ⟨by norm_num, by norm_num⟩
  have heq : Int.fract (sum_divisors_inv_pow 5 31 1)
      = Int.fract (sum_divisors_inv_pow 1829 31 1) := by
    rw [sum_divisors_inv_pow_five, sum_divisors_inv_pow_1829]
  have h5 : (5 : ℕ) = 1829 := hinj 5 1829 (by norm_num) (by norm_num) heq
  norm_num at h5
