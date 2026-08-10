import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000


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
  ¬ (∀ n : ℕ,
      (n > 1 → a n > 0) ∧
      (n > 1 ∧ n ≠ 8  →
        ∃ k : ℕ,
          0 < k ∧ k < n ∧
          Nat.Prime (2 * k + 1) ∧
          (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
          (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)))) :=
by
  intro h
  rcases (h 14).2 (by norm_num) with ⟨k, hkpos, hklt, hkprime, hkeq⟩
  interval_cases k
  · exact (by decide : ¬ ((Nat.primeCounting (1 * 14) - Nat.primeCounting ((1 - 1) * 14)) = (Nat.primeCounting ((1 + 1) * 14) - Nat.primeCounting (1 * 14)))) hkeq
  · exact (by decide : ¬ ((Nat.primeCounting (2 * 14) - Nat.primeCounting ((2 - 1) * 14)) = (Nat.primeCounting ((2 + 1) * 14) - Nat.primeCounting (2 * 14)))) hkeq
  · exact (by decide : ¬ ((Nat.primeCounting (3 * 14) - Nat.primeCounting ((3 - 1) * 14)) = (Nat.primeCounting ((3 + 1) * 14) - Nat.primeCounting (3 * 14)))) hkeq
  · exact (by decide : ¬ Nat.Prime (2 * 4 + 1)) hkprime
  · exact (by decide : ¬ ((Nat.primeCounting (5 * 14) - Nat.primeCounting ((5 - 1) * 14)) = (Nat.primeCounting ((5 + 1) * 14) - Nat.primeCounting (5 * 14)))) hkeq
  · exact (by decide : ¬ ((Nat.primeCounting (6 * 14) - Nat.primeCounting ((6 - 1) * 14)) = (Nat.primeCounting ((6 + 1) * 14) - Nat.primeCounting (6 * 14)))) hkeq
  · exact (by decide : ¬ Nat.Prime (2 * 7 + 1)) hkprime
  · exact (by decide : ¬ ((Nat.primeCounting (8 * 14) - Nat.primeCounting ((8 - 1) * 14)) = (Nat.primeCounting ((8 + 1) * 14) - Nat.primeCounting (8 * 14)))) hkeq
  · exact (by decide : ¬ ((Nat.primeCounting (9 * 14) - Nat.primeCounting ((9 - 1) * 14)) = (Nat.primeCounting ((9 + 1) * 14) - Nat.primeCounting (9 * 14)))) hkeq
  · exact (by decide : ¬ Nat.Prime (2 * 10 + 1)) hkprime
  · exact (by decide : ¬ ((Nat.primeCounting (11 * 14) - Nat.primeCounting ((11 - 1) * 14)) = (Nat.primeCounting ((11 + 1) * 14) - Nat.primeCounting (11 * 14)))) hkeq
  · exact (by decide : ¬ Nat.Prime (2 * 12 + 1)) hkprime
  · exact (by decide : ¬ Nat.Prime (2 * 13 + 1)) hkprime
