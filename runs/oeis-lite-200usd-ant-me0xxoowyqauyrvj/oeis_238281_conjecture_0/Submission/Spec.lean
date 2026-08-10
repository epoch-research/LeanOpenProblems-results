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

/-
Conjecture: (i) a(n) > 0 for all n > 1. Moreover, if n > 1 is not equal to 8, then there is a positive
integer k < n with 2*k + 1 prime such that the two intervals ((k-1)*n, k*n) and (k*n, (k+1)*n) contain
the same number of primes.

This conjecture is FALSE: the value `n = 14` is a counterexample to the second part.
For `n = 14`, the only positive integers `k < 14` for which the interval `((k-1)*14, k*14]`
contains the same number of primes as `(k*14, (k+1)*14]` are `k = 4` and `k = 12`, but for
both of these `2*k + 1` (namely `9` and `25`) fails to be prime.  Hence there is no `k < 14`
with `2*k + 1` prime achieving the required equality, contradicting the conjecture.
-/
set_option maxRecDepth 8000 in
theorem oeis_238281_conjecture_0.disproof :
  ¬ ∀ (n : ℕ),
  (n > 1 → a n > 0) ∧
  (n > 1 ∧ n ≠ 8  →
    ∃ k : ℕ,
      0 < k ∧ k < n ∧
      Nat.Prime (2 * k + 1) ∧
      (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) := by
  intro H
  obtain ⟨k, hk0, hk14, hkp, hkeq⟩ := (H 14).2 ⟨by norm_num, by norm_num⟩
  interval_cases k <;>
    first
      | (exact absurd hkp (by decide))
      | (exact absurd hkeq (by decide))

set_option maxRecDepth 8000 in
theorem foo.disproof :
  ¬ ∀ (n : ℕ),
  (n > 1 → a n > 0) ∧
  (n > 1 ∧ n ≠ 8  →
    ∃ k : ℕ,
      0 < k ∧ k < n ∧
      Nat.Prime (2 * k + 1) ∧
      (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) :=
  oeis_238281_conjecture_0.disproof
