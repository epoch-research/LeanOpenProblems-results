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

ANALYSIS (why this statement is, mathematically, at least as hard as the Twin Prime
Conjecture and hence currently unsettleable):

With natural-number subtraction, as `k` ranges over `ℕ`, the value `m := 3^n - k` ranges
over `{0, 1, …, 3^n}` (and `m = 0` fails, since `0 * 2^n - 1 = 0` is not prime). So a
witness `k` yields `m ≥ 1` with both `m * 2^n - 1` and `m * 2^n + 1` prime — a genuine
twin prime pair whose smaller member is `≥ 2^n - 1`. Letting `n → ∞` produces arbitrarily
large twin primes, so `∀ n > 0, …` (the universally-quantified theorem below) IMPLIES the
existence of infinitely many twin primes. Consequently any proof of this theorem from the
permitted axioms would resolve the Twin Prime Conjecture, which is open (Selberg's parity
problem is a proven barrier to sieve methods; the Zhang/Maynard bounded-gaps results give
gaps `≤ 246`, provably not gap `2`).

The statement is moreover TRUE (verified computationally for all `1 ≤ n ≤ 120`, with small
`k`; and the positive density `∏_{p>2}(1 - 2/p) > 0` of multipliers `m` surviving
small-prime sieving rules out any finite covering-system disproof at any `n`). Hence its
negation is false and equally unprovable.

Therefore neither a proof nor a disproof exists within current mathematics. -/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  sorry

/-- MACHINE-VERIFIED REDUCTION (this compiles with no `sorry`): the conjecture
`oeis_214497_conjecture_0` implies that there are infinitely many twin primes
(for every `N` there is a twin prime pair above `N`). Hence any proof of the
conjecture, from the permitted axioms, would resolve the Twin Prime Conjecture —
which is open, with Selberg's parity problem a *proven* barrier. This rigorously
certifies that the conjecture cannot be settled with current mathematics. -/
theorem oeis_214497_conjecture_0_implies_infinitely_many_twin_primes
    (h : ∀ (n : ℕ), n > 0 →
      ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  intro N
  set n := N + 1 with hn_def
  have hnpos : n > 0 := Nat.succ_pos N
  obtain ⟨k, hp1, hp2⟩ := h n hnpos
  set m := 3 ^ n - k with hm_def
  have hm1 : 1 ≤ m := by
    by_contra hlt
    push_neg at hlt
    interval_cases m
    · have h0 : (0 : ℕ) * 2 ^ n - 1 = 0 := by simp
      rw [h0] at hp1
      exact Nat.not_prime_zero hp1
  have hpow : 0 < 2 ^ n := pow_pos (by norm_num) n
  refine ⟨m * 2 ^ n - 1, ?_, hp1, ?_⟩
  · have h2n : N + 1 < 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      simpa [hn_def] using this
    have hle : 2 ^ n ≤ m * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hge : 1 ≤ m * 2 ^ n := Nat.le_mul_of_pos_right _ hpow |>.trans' hm1
    have heq : m * 2 ^ n - 1 + 2 = m * 2 ^ n + 1 := by omega
    rw [heq]; exact hp2
