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
Disproof of the conjectured statement: it fails at `n = 14`.
For `n = 14`, the prime counting function at multiples of 14 takes values
π(0)=0, π(14)=6, π(28)=9, π(42)=13, π(56)=16, π(70)=19, π(84)=23, π(98)=25,
π(112)=29, π(126)=30, π(140)=34, π(154)=36, π(168)=39, giving consecutive
differences 6,3,4,3,3,4,2,4,1,4,2,3.  For each `0 < k < 14` with `2k+1`
prime (k ∈ {1,2,3,5,6,8,9,11}), the two consecutive differences at `k`
differ, so the second conjunct fails for `n = 14`.
-/
theorem oeis_238281_conjecture_0.disproof :
  ¬ ∀ (n : ℕ),
  (n > 1 → a n > 0) ∧
  (n > 1 ∧ n ≠ 8  →
    ∃ k : ℕ,
      0 < k ∧ k < n ∧
      Nat.Prime (2 * k + 1) ∧
      (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) := by
  intro h
  obtain ⟨-, h2⟩ := h 14
  obtain ⟨k, hk0, hk14, hp, heq⟩ := h2 ⟨by norm_num, by norm_num⟩
  set_option maxRecDepth 20000 in
  interval_cases k <;> revert hp heq <;> decide
