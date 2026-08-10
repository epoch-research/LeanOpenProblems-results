import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

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

theorem oeis_238281_conjecture_0.disproof :
  ¬ ∀ n : ℕ,
    (n > 1 → a n > 0) ∧
    (n > 1 ∧ n ≠ 8  →
      ∃ k : ℕ,
        0 < k ∧ k < n ∧
        Nat.Prime (2 * k + 1) ∧
        (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
        (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) := by
  intro h
  have h14 := h 14
  have h14_cond : 14 > 1 ∧ 14 ≠ 8 := by decide
  have h14_exists := h14.2 h14_cond
  rcases h14_exists with ⟨k, hk1, hk2, hk3, hk4⟩
  interval_cases k
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
  · revert hk3 hk4; decide
