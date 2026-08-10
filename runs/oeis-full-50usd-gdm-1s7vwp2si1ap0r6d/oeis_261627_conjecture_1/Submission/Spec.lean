import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A261627: Number of primes $p$ such that $n-(p \cdot n'-1)$ and $n+(p \cdot n'-1)$ are both prime,
where $n'$ is 1 or 2 according as $n$ is odd or even.
-/
noncomputable def A261627 (n : ℕ) : ℕ :=
  let n' : ℕ := if n % 2 = 1 then 1 else 2

  -- The set of relevant primes is constructed by filtering primes below $n+1$.
  Finset.card $ Finset.filter (fun p : ℕ =>
    let k := p * n' - 1
    -- Condition k < n ensures that the subtraction is valid in Nat.
    -- Primality check ensures n - k >= 2.
    k < n ∧
    Nat.Prime (n - k) ∧
    Nat.Prime (n + k)
  ) (primesBelow (n + 1))

-- Formal definition of the strong Goldbach conjecture (every even number >= 4 is a sum of two primes).
def goldbach_conjecture : Prop :=
  ∀ (m : ℕ), 4 ≤ m ∧ Even m →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q

-- Formal definition of Lemoine's conjecture (every odd number >= 7 is p + 2q for primes p, q).
def lemoine_conjecture : Prop :=
  ∀ (n : ℕ), 7 ≤ n ∧ Odd n →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + 2 * q

-- Formal statement of the A261627 main conjecture (a(n) > 0 for n > 6).
def A261627_conjecture : Prop :=
  ∀ (n : ℕ), 6 < n → 0 < A261627 n

lemma unpack_A261627 {n : ℕ} (h : 0 < A261627 n) :
  ∃ p, p ∈ primesBelow (n + 1) ∧
    let n' : ℕ := if n % 2 = 1 then 1 else 2
    let k := p * n' - 1
    k < n ∧ Nat.Prime (n - k) ∧ Nat.Prime (n + k) := by
  unfold A261627 at h
  rcases Finset.card_pos.mp h with ⟨p, hp⟩
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hp_prime, hp_cond⟩
  exact ⟨p, hp_prime, hp_cond⟩

/--
Conjecture: This is stronger than Goldbach's conjecture (A002375) and Lemoine's conjecture (A046927).
This formalizes the statement that the main A261627 conjecture implies both Goldbach's and Lemoine's conjectures.
-/
theorem oeis_261627_conjecture_1 : A261627_conjecture → goldbach_conjecture ∧ lemoine_conjecture := by
  intro h_conj
  constructor
  · -- goldbach_conjecture
    intro m ⟨h4, he⟩
    rcases he with ⟨k, rfl⟩
    -- Since m is even, m = k + k = 2 * k.
    have h_cases : 2 * k = 4 ∨ 2 * k = 6 ∨ 8 ≤ 2 * k := by omega
    rcases h_cases with h4_eq | h6_eq | h8_le
    · -- m = 4
      use 2, 2
      refine ⟨by decide, by decide, ?_⟩
      omega
    · -- m = 6
      use 3, 3
      refine ⟨by decide, by decide, ?_⟩
      omega
    · -- m >= 8
      let n := 2 * k - 1
      have hn6 : 6 < n := by omega
      have hn_odd : n % 2 = 1 := by
        -- Since n = 2 * k - 1 and 8 <= 2 * k, we can prove n % 2 = 1.
        omega
      have hn_prime : 0 < A261627 n := h_conj n hn6
      rcases unpack_A261627 hn_prime with ⟨p, hp_below, hp_cond⟩
      have hp_is_prime : Nat.Prime p := by
        rw [Nat.mem_primesBelow] at hp_below
        exact hp_below.2
      have hp_ge2 : 2 ≤ p := hp_is_prime.two_le
      have hn'_eq : (if n % 2 = 1 then 1 else 2) = 1 := by rw [if_pos hn_odd]
      dsimp only at hp_cond
      rw [hn'_eq] at hp_cond
      rcases hp_cond with ⟨hk, h_prime_sub, h_prime_add⟩
      -- Since hn'_eq is 1, let's look at k' in hp_cond.
      -- k' = p * 1 - 1 = p - 1.
      have hk_eq : p * 1 - 1 = p - 1 := by omega
      rw [hk_eq] at hk h_prime_sub
      -- We want to prove that m = p + (n - (p - 1)).
      use p, n - (p - 1)
      refine ⟨hp_is_prime, h_prime_sub, ?_⟩
      omega
  · -- lemoine_conjecture
    intro m ⟨h7, ho⟩
    rcases ho with ⟨k, rfl⟩
    -- Since m is odd, m = 2 * k + 1.
    have h_cases : 2 * k + 1 = 7 ∨ 9 ≤ 2 * k + 1 := by omega
    rcases h_cases with h7_eq | h9_le
    · -- m = 7
      use 3, 2
      refine ⟨by decide, by decide, ?_⟩
      omega
    · -- m >= 9
      let n := 2 * k
      have hn6 : 6 < n := by omega
      have hn_even : n % 2 = 0 := by omega
      have hn_not_odd : ¬(n % 2 = 1) := by omega
      have hn_prime : 0 < A261627 n := h_conj n hn6
      rcases unpack_A261627 hn_prime with ⟨q, hq_below, hq_cond⟩
      have hq_is_prime : Nat.Prime q := by
        rw [Nat.mem_primesBelow] at hq_below
        exact hq_below.2
      have hq_ge2 : 2 ≤ q := hq_is_prime.two_le
      have hn'_eq : (if n % 2 = 1 then 1 else 2) = 2 := by rw [if_neg hn_not_odd]
      dsimp only at hq_cond
      rw [hn'_eq] at hq_cond
      rcases hq_cond with ⟨hk, h_prime_sub, h_prime_add⟩
      -- k = q * 2 - 1 = 2 * q - 1.
      have hk_eq : q * 2 - 1 = 2 * q - 1 := by omega
      rw [hk_eq] at hk h_prime_sub
      use n - (2 * q - 1), q
      refine ⟨h_prime_sub, hq_is_prime, ?_⟩
      omega
