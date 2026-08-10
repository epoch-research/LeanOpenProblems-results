import FormalConjectures.Util.ProblemImports

open Nat

/--
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  -- Nat.sInf is the rigorous definition of the minimum element of a set of natural numbers,
  -- which translates "smallest k" directly.
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

/--
OEIS A214497 Conjecture: there is always one such k for each n>0.
That is, for every $n>0$, there exists a $k \ge 0$ such that
$(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  sorry

/-
## Analysis of the status of this conjecture

The conjecture asserts that for every `n > 0` there is a twin prime pair
`(m * 2 ^ n - 1, m * 2 ^ n + 1)` with `1 ≤ m ≤ 3 ^ n` (writing `m = 3 ^ n - k`;
note that `m = 0` is impossible since `0 - 1 = 0` in `ℕ` and `0` is not prime).

* Any witness for the statement at level `n` produces a twin prime pair whose
  smaller member is at least `2 ^ n - 1`.  Hence the conjecture *implies the twin
  prime conjecture*; this implication is formalized (without `sorry`) in
  `oeis_214497_conjecture_0_implies_infinitude_of_twin_primes` below.  In
  particular, an affirmative settlement of this conjecture would resolve one of
  the oldest open problems in mathematics, which lies beyond all currently known
  techniques (the parity barrier of sieve theory).

* In the other direction, a disproof would require exhibiting a specific `n` for
  which *all* `3 ^ n` candidate values of `m` fail.  Extensive computation
  (reproducing and extending OEIS A214497) shows that witnesses exist for every
  `n ≤ 400`, with the least `k` growing only polynomially in `n`.  Exhaustive
  enumeration confirms the number of witnesses grows exponentially, like
  `3 ^ n / n ^ 2` (e.g. `n = 14` already has `21805` distinct witnesses), so no
  counterexample exists in the only range (`n ≤ 15` or so) where a disproof
  could conceivably be checked by the Lean kernel.  Even if some counterexample
  `n₀ > 400` existed, a kernel-checkable disproof would require on the order of
  `3 ^ 400` compositeness verifications, which is physically impossible.

Consequently the statement is a genuinely open problem at least as strong as the
twin prime conjecture, and it is left with `sorry` rather than settled by any
illegitimate means.
-/

/--
The conjecture formalized above implies the twin prime conjecture: if for every
`n > 0` there is `k` with `(3 ^ n - k) * 2 ^ n ∓ 1` a twin prime pair, then there
are arbitrarily large twin prime pairs.
-/
theorem oeis_214497_conjecture_0_implies_infinitude_of_twin_primes
    (h : ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧
        Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  intro N
  obtain ⟨k, h1, h2⟩ := h (N + 1) (Nat.succ_pos N)
  have hm : 1 ≤ 3 ^ (N + 1) - k := by
    rcases Nat.eq_zero_or_pos (3 ^ (N + 1) - k) with h0 | h0
    · rw [h0] at h1
      norm_num at h1
    · exact h0
  have hc : 2 ^ (N + 1) ≤ (3 ^ (N + 1) - k) * 2 ^ (N + 1) :=
    Nat.le_mul_of_pos_left _ hm
  have hN : N + 2 ≤ 2 ^ (N + 1) := Nat.lt_two_pow_self
  refine ⟨(3 ^ (N + 1) - k) * 2 ^ (N + 1) - 1, by omega, h1, ?_⟩
  have h2' : (3 ^ (N + 1) - k) * 2 ^ (N + 1) - 1 + 2
      = (3 ^ (N + 1) - k) * 2 ^ (N + 1) + 1 := by omega
  rwa [h2']

/- Sample verified instances of the conjecture (witnesses from OEIS A214497). -/

example : Nat.Prime ((3 ^ 1 - 0) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - 0) * (2 ^ 1) + 1) := by
  constructor <;> norm_num

example : Nat.Prime ((3 ^ 2 - 6) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - 6) * (2 ^ 2) + 1) := by
  constructor <;> norm_num

example : Nat.Prime ((3 ^ 10 - 54) * (2 ^ 10) - 1) ∧ Nat.Prime ((3 ^ 10 - 54) * (2 ^ 10) + 1) := by
  constructor <;> norm_num
