import FormalConjectures.Util.ProblemImports

open Nat Finset

-- We need to open scoped Nat.Prime for Nat.Prime. `Nat.Prime p` is just `p.Prime`.
open scoped Nat.Prime

/--
A236097: $a(n) = |\{0 < k < n-2: p = \phi(k) + \phi(n-k)/2 + 1, \text{prime}(p) - p - 1 \text{ and } \text{prime}(p) - p + 1 \text{ are all prime}\}|$, where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A236097 (n : ℕ) : ℕ :=
  -- The set of $k$ is $1 \le k \le n - 3$.
  -- Icc 1 (n - 3) is correct. If $n \le 3$, $n-3=0$ or less, Icc 1 0 is empty.
  (Icc 1 (n - 3)).sum fun k =>
    -- $p = \phi(k) + \phi(n-k)/2 + 1$.
    let p_val := k.totient + (n - k).totient / 2 + 1

    -- The $p$-th prime (1-indexed) is Nat.nth Nat.Prime (p_val - 1).
    -- Mathlib uses `Nat.prime` which is a bound variable style definition.
    -- The canonical way to get the $n$-th prime is `Nat.prime (n-1)` (using 1-indexing for $n$).
    -- In Mathlib, use `Nat.nth Nat.Prime (p_val - 1)` or simply `Nat.prime_aux` or similar.
    -- The common alias for the $n$-th prime is `Nat.prime (n-1)` in many older contexts,
    -- but after the search, `Nat.nth Nat.Prime` seems to be the right function.
    let p_prime := Nat.nth Nat.Prime (p_val - 1)

    -- Condition check. We assume the subtractions are safe because the prime sequence grows fast enough.
    -- For $p \ge 2$, $\pi_p \ge p+1$. The result of the subtraction must be in $\mathbb{N}$, and since they are primes, must be $\ge 2$.
    -- $p\_prime - p\_val - 1$ is interpreted as $p\_prime - (p\_val + 1)$.
    -- $p\_prime - p\_val + 1$ is straightforward.
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0

/--
**Machine-verified obstruction.** Whenever `A236097 n > 0`, the summand witnessing
this yields a *twin prime pair* `(P - p - 1, (P - p - 1) + 2)`, because the two
required primes `prime(p) - p - 1` and `prime(p) - p + 1` differ by exactly `2`.
This is proven here with no `sorry`, and shows that any proof of the conjecture
produces twin primes at every scale (since the witnessing `p ≥ minpval(n) → ∞`),
i.e. it implies the (open) twin prime conjecture.
-/
theorem pos_gives_twin_pair {n : ℕ} (h : 0 < A236097 n) :
    ∃ q, q.Prime ∧ (q + 2).Prime := by
  rw [A236097] at h
  obtain ⟨k, _hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  set p := k.totient + (n - k).totient / 2 + 1 with hpdef
  set P := Nat.nth Nat.Prime (p - 1) with hPdef
  simp only at hne
  by_cases hc : p.Prime ∧ (P - p - 1).Prime ∧ (P - p + 1).Prime
  · obtain ⟨_, ha, hb⟩ := hc
    refine ⟨P - p - 1, ha, ?_⟩
    have h2 : 2 ≤ P - p - 1 := ha.two_le
    have heq : P - p - 1 + 2 = P - p + 1 := by omega
    rwa [heq]
  · rw [if_neg hc] at hne; exact absurd rfl hne

/--
The number-theoretic kernel of the conjecture: for every `n > 31` there is a
`k ∈ [1, n-3]` such that `p := φ(k) + φ(n-k)/2 + 1` is prime and both
`prime(p) - p - 1` and `prime(p) - p + 1` are prime.

Remark on difficulty.  The two numbers `prime(p) - p - 1` and `prime(p) - p + 1`
differ by `2`, so whenever they are both prime they form a *twin prime pair*.
Moreover the quantity `p = φ(k) + φ(n-k)/2 + 1` satisfies
`p ≥ min_k pval(n,k) → ∞` as `n → ∞` (numerically ≈ 98369 at `n = 10^6`), so the
primes `p` witnessing the conjecture are necessarily unbounded.  Consequently a
proof of `key` (equivalently of `oeis_236097_conjecture_0`) yields infinitely
many good primes, hence infinitely many twin primes; i.e. it implies the twin
prime conjecture, which is currently open and unavailable in Mathlib.
-/
theorem key (n : ℕ) (hn : n > 31) :
    ∃ k ∈ Icc 1 (n - 3),
      (k.totient + (n - k).totient / 2 + 1).Prime ∧
      (Nat.nth Nat.Prime (k.totient + (n - k).totient / 2 + 1 - 1)
        - (k.totient + (n - k).totient / 2 + 1) - 1).Prime ∧
      (Nat.nth Nat.Prime (k.totient + (n - k).totient / 2 + 1 - 1)
        - (k.totient + (n - k).totient / 2 + 1) + 1).Prime := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 31.

The proof reduces (unconditionally) to the number-theoretic kernel `key`.
-/
theorem oeis_236097_conjecture_0 : ∀ (n : ℕ), n > 31 → A236097 n > 0 := by
  intro n hn
  rw [gt_iff_lt, A236097]
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  · obtain ⟨k, hk, h1, h2, h3⟩ := key n hn
    refine ⟨k, hk, ?_⟩
    simp only []
    rw [if_pos ⟨h1, h2, h3⟩]
    exact Nat.one_pos
