import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219055: Number of ways to write $n = p+q(3-(-1)^n)/2$ with $p>q$ and $p, q, p-6, q+6$ all prime.
-/
def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    -- c = 1 + n % 2. The condition p > q is equivalent to (c + 1) * q < n.
    ((1 + n % 2) + 1) * q < n ∧

    -- Primality conditions for q and derived terms
    q.Prime ∧
    (q + 6).Prime ∧

    -- Primality conditions for p = n - c * q and p - 6
    (n - (1 + n % 2) * q).Prime ∧        -- p must be prime
    (n - (1 + n % 2) * q - 6).Prime      -- p - 6 must be prime
  ) (Finset.range n)

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0


-- The finite checks are split into blocks of one hundred to keep kernel
-- reduction small.  The local instance uses the least-prime-factor test.
section FiniteChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local instance] Nat.decidablePrime'
private def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]
private theorem goldbach_check : ∀ a : Fin 81, ∀ b : Fin 100,
    let n := a.val * 100 + b.val
    4 ≤ n → n ≤ 8012 → Even n →
    ∃ p ∈ smallPrimes, p.Prime ∧ (n-p).Prime ∧ p ≤ n := by
  intro a
  fin_cases a <;> decide +kernel

private theorem lemoine_check : ∀ a : Fin 158, ∀ b : Fin 100,
    let n := a.val * 100 + b.val
    7 ≤ n → n ≤ 15727 → Odd n →
    ∃ q ∈ smallPrimes, q.Prime ∧ (n-2*q).Prime ∧ 2*q ≤ n := by
  intro a
  fin_cases a <;> decide +kernel

end FiniteChecks

private theorem a219055_witness {n : ℕ} (h : 0 < A219055 n) :
    ∃ q : ℕ, ((1 + n % 2) + 1) * q < n ∧ q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧ (n - (1 + n % 2) * q - 6).Prime := by
  obtain ⟨q, hq⟩ := Finset.card_pos.mp h
  exact ⟨q, (Finset.mem_filter.mp hq).2⟩

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture :=
  by
    intro h
    refine ⟨?_, ?_, ?_⟩
    · intro n hn heven
      by_cases hsmall : n ≤ 8012
      · have hc := goldbach_check ⟨n / 100, by omega⟩
          ⟨n % 100, Nat.mod_lt _ (by decide)⟩
        have heq : n / 100 * 100 + n % 100 = n := by omega
        change 4 ≤ n / 100 * 100 + n % 100 →
          n / 100 * 100 + n % 100 ≤ 8012 →
          Even (n / 100 * 100 + n % 100) → _ at hc
        rw [heq] at hc
        obtain ⟨p, _, hp, hq, hle⟩ := hc hn hsmall heven
        exact ⟨p, n - p, hp, hq, by omega⟩
      · obtain ⟨q, hlt, hq, _, hp, _⟩ :=
          a219055_witness (h n (Or.inl ⟨heven, by omega⟩))
        rw [Nat.even_iff.mp heven] at hlt hp
        simp only [Nat.add_zero, Nat.one_mul] at hlt hp
        exact ⟨n - q, q, hp, hq, by omega⟩
    · intro n hn hodd
      by_cases hsmall : n ≤ 15727
      · have hc := lemoine_check ⟨n / 100, by omega⟩
          ⟨n % 100, Nat.mod_lt _ (by decide)⟩
        have heq : n / 100 * 100 + n % 100 = n := by omega
        change 7 ≤ n / 100 * 100 + n % 100 →
          n / 100 * 100 + n % 100 ≤ 15727 →
          Odd (n / 100 * 100 + n % 100) → _ at hc
        rw [heq] at hc
        obtain ⟨q, _, hq, hp, hle⟩ := hc hn hsmall hodd
        exact ⟨n - 2 * q, q, hp, hq, by omega⟩
      · obtain ⟨q, hlt, hq, _, hp, _⟩ :=
          a219055_witness (h n (Or.inr ⟨hodd, by omega⟩))
        rw [Nat.odd_iff.mp hodd] at hlt hp
        norm_num only at hlt hp
        exact ⟨n - 2 * q, q, hp, hq, by omega⟩
    · apply Set.infinite_of_not_bddAbove
      rw [not_bddAbove_iff]
      intro b
      let n := 2 * (b + 8013)
      have hn : Even n := ⟨b + 8013, by dsimp [n]; omega⟩
      have hlarge : 8012 < n := by dsimp [n]; omega
      obtain ⟨q, hlt, hq, hq6, hp, hp6⟩ :=
        a219055_witness (h n (Or.inl ⟨hn, hlarge⟩))
      rw [Nat.even_iff.mp hn] at hlt hp hp6
      simp only [Nat.add_zero, Nat.one_mul] at hlt hp hp6
      by_cases hb : b < q
      · exact ⟨q, ⟨hq, hq6⟩, hb⟩
      · refine ⟨n - q - 6, ⟨hp6, ?_⟩, ?_⟩
        · have heq : n - q - 6 + 6 = n - q := by dsimp [n] at *; omega
          rwa [heq]
        · dsimp [n] at *
          omega

theorem oeis_219055_conjecture_1.disproof : ¬ (type_of% @oeis_219055_conjecture_1) := sorry
