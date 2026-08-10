import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

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
  have h14 := h 14
  rcases h14 with ⟨_, h2⟩
  have h_prem : 14 > 1 ∧ 14 ≠ 8 := by decide
  have h_ex := h2 h_prem
  rcases h_ex with ⟨k, hk_gt, hk_lt, hk_prime, hk_eq⟩
  interval_cases k
  · revert hk_eq; decide
  · revert hk_eq; decide
  · revert hk_eq; decide
  · revert hk_prime; decide
  · revert hk_eq; decide
  · revert hk_eq; decide
  · revert hk_prime; decide
  · revert hk_eq; decide
  · revert hk_eq; decide
  · revert hk_prime; decide
  · revert hk_eq; decide
  · revert hk_prime; decide
  · revert hk_prime; decide
