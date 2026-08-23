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

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- There is no `k < 14` with `2k+1` prime giving equal prime counts on the two adjacent intervals. -/
private lemma no_special_k_for_14 :
    ∀ k : Fin 14,
      ¬ (0 < (k : ℕ) ∧ Nat.Prime (2 * (k : ℕ) + 1) ∧
        Nat.primeCounting ((k : ℕ) * 14) - Nat.primeCounting (((k : ℕ) - 1) * 14) =
        Nat.primeCounting (((k : ℕ) + 1) * 14) - Nat.primeCounting ((k : ℕ) * 14)) := by
  decide

/--
The second part of the conjecture fails at `n = 14`: there is no positive integer `k < 14`
with `2 * k + 1` prime such that `((k-1)*14, k*14]` and `(k*14, (k+1)*14]` contain equally
many primes.
-/
theorem oeis_238281_conjecture_0.disproof :
    ¬ (∀ (n : ℕ),
      (n > 1 → a n > 0) ∧
      (n > 1 ∧ n ≠ 8  →
        ∃ k : ℕ,
          0 < k ∧ k < n ∧
          Nat.Prime (2 * k + 1) ∧
          (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
          (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)))) := by
  intro h
  obtain ⟨k, hk0, hkn, hp, heq⟩ := (h 14).2 (by decide)
  exact no_special_k_for_14 ⟨k, hkn⟩ ⟨hk0, hp, heq⟩
