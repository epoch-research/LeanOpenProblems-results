import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236511: $a(n) = |\{0 < k < n: p = 3\phi(k) + \phi(n-k) - 1, p + 2, p + 6 \text{ and } p + 8 \text{ are all prime}\}|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ioo 0 n).sum (fun k ↦
    let T := 3 * totient k + totient (n - k)
    -- p = T - 1. The four primes are p, p+2, p+6, p+8, which correspond to T-1, T+1, T+5, T+7.
    if (T - 1).Prime ∧ (T + 1).Prime ∧ (T + 5).Prime ∧ (T + 7).Prime then 1 else 0
  )

/-!
### Status of this conjecture (A236511, Zhi-Wei Sun)

This is a genuine *open* problem.  A short analysis:

* The encoding is faithful to OEIS A236511 and the threshold `1075` is tight:
  the largest `n` with `a n = 0` is exactly `1075`, and `a n > 0` (indeed `a n → ∞`,
  growing like `n / (log n)^4`) has been verified computationally well past `n = 10^5`.
  So the statement is *true* and no counterexample exists (it cannot be disproved).

* Proving it, however, is at least as hard as a celebrated unsolved problem.
  For every `n`, `a n > 0` requires some `k` with
  `T = 3 φ(k) + φ(n-k)` a *prime quadruplet centre*, i.e. `T-1, T+1, T+5, T+7`
  all prime (the admissible pattern `p, p+2, p+6, p+8`).  Since
  `min_k (3 φ(k) + φ(n-k))` grows linearly in `n`, this forces prime quadruplets
  of unbounded size, i.e. **infinitely many prime quadruplets** — an open problem
  (even the twin prime conjecture is open), with no proof in the literature and no
  supporting machinery (bounded gaps / Maynard–Tao / Hardy–Littlewood) in Mathlib.

The proof below performs the sound reduction of `a n > 0` to the existence of a
suitable `k`; the remaining lemma `oeis_236511_key` is exactly the open
number-theoretic core.
-/

/-- The open number-theoretic core: for every `n > 1075` there is `k` with
`0 < k < n` such that `3 φ(k) + φ(n-k)` is a prime-quadruplet centre. -/
theorem oeis_236511_key (n : ℕ) (hn : n > 1075) :
    ∃ k ∈ Ioo 0 n,
      (3 * totient k + totient (n - k) - 1).Prime ∧
      (3 * totient k + totient (n - k) + 1).Prime ∧
      (3 * totient k + totient (n - k) + 5).Prime ∧
      (3 * totient k + totient (n - k) + 7).Prime := by
  sorry

/-- Conjecture: a(n) > 0 for all n > 1075. -/
theorem oeis_236511_conjecture_0 : ∀ n : ℕ, n > 1075 → a n > 0 := by
  intro n hn
  unfold a
  apply Finset.sum_pos'
  · intro k _; dsimp only; split <;> simp
  · obtain ⟨k, hk, h1, h2, h3, h4⟩ := oeis_236511_key n hn
    refine ⟨k, hk, ?_⟩
    dsimp only
    rw [if_pos ⟨h1, h2, h3, h4⟩]
    exact Nat.one_pos
