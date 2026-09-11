import FormalConjectures.Util.ProblemImports

/--
A238281: $a(n) = |\left\{0 < k < n: \text{the two intervals } (k \cdot n, (k+1) \cdot n) \text{ and } ((k+1) \cdot n, (k+2) \cdot n) \text{ contain the same number of primes}\right\}|$.
The sequence $a(n)$ counts the number of positive integers $k < n$ such that the number of primes in
$(k \cdot n, (k+1) \cdot n]$ is equal to the number of primes in $((k+1) \cdot n, (k+2) \cdot n]$,
where the number of primes in $(a, b]$ is $\text{Nat.primeCounting } b - \text{Nat.primeCounting } a$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter
    (fun k : ℕ =>
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)) =
      (Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n)))
    (Finset.Ico 1 n)

/--
Conjecture: (i) a(n) > 0 for all n > 1. Moreover, if n > 1 is not equal to 8, then there is a positive
integer k < n with 2*k + 1 prime such that the two intervals ((k-1)*n, k*n) and (k*n, (k+1)*n) contain
the same number of primes.
-/
theorem oeis_238281_conjecture_0 (n : ℕ) :
  (n > 1 → a n > 0) ∧
  (n > 1 ∧ n ≠ 8  →
    ∃ k : ℕ,
      0 < k ∧ k < n ∧
      Nat.Prime (2 * k + 1) ∧
      (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) :=
by sorry

/- For `n = 14` there is no `k` with `0 < k < 14`, `2k+1` prime, such that the intervals
`((k-1)·14, k·14]` and `(k·14, (k+1)·14]` contain the same number of primes.
(Verified by computation: the pairs of prime counts are
k=1: (6,3), k=2: (3,4), k=3: (4,3), k=5: (3,4), k=6: (4,2), k=8: (4,1), k=9: (1,4), k=11: (2,3).) -/
set_option maxRecDepth 100000 in
theorem oeis_238281_aux14 : ∀ k, k < 14 → 0 < k → Nat.Prime (2 * k + 1) →
    (Nat.primeCounting (k * 14) - Nat.primeCounting ((k - 1) * 14)) =
      (Nat.primeCounting ((k + 1) * 14) - Nat.primeCounting (k * 14)) → False := by
  decide

theorem oeis_238281_conjecture_0.disproof : ¬ (type_of% @oeis_238281_conjecture_0) := by
  intro h
  obtain ⟨_, h2⟩ := h 14
  obtain ⟨k, hk0, hkn, hp, heq⟩ := h2 ⟨by norm_num, by norm_num⟩
  exact oeis_238281_aux14 k hkn hk0 hp heq
