import FormalConjectures.Util.ProblemImports

open Finset Nat Set Classical

/--
The number of partitions of $m$ into $n$ distinct primes.
This is defined by counting subsets of primes $S$ such that $|S|=n$ and $\sum_{p \in S} p = m$.
The set of candidate primes must include primes up to $m$.
-/
def count_distinct_prime_partitions (m n : ℕ) : ℕ :=
  let all_primes_le_m : Finset ℕ := Nat.primesBelow (m + 1)
  (all_primes_le_m.powerset.filter (fun S => S.card = n ∧ S.sum id = m)).card

/--
A344989: Smallest number whose number of partitions into $n$ distinct primes is $n$, or zero if there are no such partitions.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- S is the set of natural numbers m satisfying the condition.
    let S : Set ℕ := {m : ℕ | count_distinct_prime_partitions m n = n}
    -- sInf S computes the smallest element of S. If S is empty, sInf S = 0 for Nat.
    sInf S

/-- Auxiliary fact: for `n > 0`, there is no partition of `0` into `n` distinct primes. -/
lemma count_zero (n : ℕ) (hn : 0 < n) : count_distinct_prime_partitions 0 n = 0 := by
  simp only [count_distinct_prime_partitions]
  have h1 : Nat.primesBelow (0 + 1) = ∅ := by decide
  rw [h1, Finset.powerset_empty]
  simp
  omega

/--
Conjecture based on OEIS A344989 commentary by David A. Corneth:
$a(n) = 0$ if $2n$ consecutive integers can be written in strictly more than $n$ ways
as a sum of $n$ distinct primes and up to that point no positive integer has exactly $n$ such ways.
-/
theorem A344989_conjecture_heuristic_zero (n : ℕ) (hn : 0 < n):
  (∃ k : ℕ,
      -- Condition 1: 2n consecutive integers m > k have strictly more than n partitions.
      (∀ m : ℕ, k < m ∧ m ≤ k + 2 * n → count_distinct_prime_partitions m n > n)
      ∧
      -- Condition 2: No integer m' up to k (with m' > 0) has exactly n partitions.
      (∀ m' : ℕ, m' ≤ k → m' = 0 ∨ count_distinct_prime_partitions m' n ≠ n)
  ) → a n = 0 := by
  rintro ⟨k, hwin, hbel⟩
  unfold a
  rw [if_neg hn.ne']
  rw [sInf_eq_zero]
  right
  rw [Set.eq_empty_iff_forall_notMem]
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx⟩ := hne
  have hNE : {m : ℕ | count_distinct_prime_partitions m n = n}.Nonempty := ⟨x, hx⟩
  set m0 := sInf {m : ℕ | count_distinct_prime_partitions m n = n} with hm0
  have hm0mem : m0 ∈ {m : ℕ | count_distinct_prime_partitions m n = n} := Nat.sInf_mem hNE
  have hcount0 : count_distinct_prime_partitions m0 n = n := hm0mem
  have hm0pos : 0 < m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · exfalso; rw [h, count_zero n hn] at hcount0; omega
    · exact h
  have hk_lt : k < m0 := by
    by_contra hkm
    push_neg at hkm
    rcases hbel m0 hkm with h0 | hcne
    · omega
    · exact hcne hcount0
  by_cases hle : m0 ≤ k + 2*n
  · -- Easy case: m0 lies inside the window, so `count m0 n > n`, contradicting `= n`.
    have := hwin m0 ⟨hk_lt, hle⟩
    rw [hcount0] at this
    exact (lt_irrefl n) this
  · -- Hard case: `k + 2n < m0`, i.e. the entire window sits strictly below `m0`.
    -- The remaining goal is equivalent to the OEIS-acknowledged *heuristic* core of A344989:
    -- there is no run of `2n` consecutive integers below `m0` all having `count > n`.
    -- Via the identity `count v (n-1) = count (v+2) n` (for `v ≢ n mod 2`) and the
    -- largest-prime injection `count m0 n ≥ count (m0 - p) (n-1) = count (m0 - p + 2) n`,
    -- this reduces to the existence of a prime `p` in an interval of ratio `< 2`, i.e. to
    -- prime-gap bounds (Legendre-conjecture strength) unavailable in Mathlib and unproven
    -- in mathematics. This is the genuine open analytic core of the conjecture.
    push_neg at hle
    sorry
