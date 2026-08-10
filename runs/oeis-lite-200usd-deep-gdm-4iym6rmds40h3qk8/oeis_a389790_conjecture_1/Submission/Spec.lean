import FormalConjectures.Util.ProblemImports
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  -- The finset range is taken from the original user code.
  let R := Finset.range n

  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)



/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
lemma next_prime_mem (r : ℕ) : next_prime r ∈ {k : ℕ | Nat.Prime k ∧ r < k} := by
  have h_nonempty : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, h_le, h_prime⟩ := Nat.exists_infinite_primes (r + 1)
    use p
    simp only [Set.mem_setOf_eq]
    exact ⟨h_prime, by omega⟩
  exact Nat.sInf_mem h_nonempty

theorem next_prime_prime (r : ℕ) : Nat.Prime (next_prime r) :=
  (next_prime_mem r).1

theorem next_prime_gt (r : ℕ) : r < next_prime r :=
  (next_prime_mem r).2

theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  sorry
