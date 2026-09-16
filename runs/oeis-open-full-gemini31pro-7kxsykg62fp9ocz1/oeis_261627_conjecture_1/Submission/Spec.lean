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

/--
Conjecture: This is stronger than Goldbach's conjecture (A002375) and Lemoine's conjecture (A046927).
This formalizes the statement that the main A261627 conjecture implies both Goldbach's and Lemoine's conjectures.
-/
lemma goldbach_from_A26 (h : A261627_conjecture) : goldbach_conjecture := by
  intro m hm
  rcases hm with ⟨hm4, hm_even⟩
  have ⟨k, hk⟩ := hm_even
  have hk2 : 2 ≤ k := by omega
  by_cases hk_lt : k < 7
  · interval_cases k
    · use 2, 2; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 3; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 5; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 7; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 5, 7; refine ⟨by norm_num, by norm_num, by omega⟩
  · have hk_ge : 7 ≤ k := by omega
    have h_n : 6 < m / 2 := by omega
    have h_a26 := h (m / 2) h_n
    unfold A261627 at h_a26
    have h_pos : 0 < (filter (fun p =>
      let k := p * (if (m / 2) % 2 = 1 then 1 else 2) - 1
      k < m / 2 ∧ (m / 2 - k).Prime ∧ (m / 2 + k).Prime) (primesBelow (m / 2 + 1))).card := h_a26
    rw [Finset.card_pos] at h_pos
    rcases h_pos with ⟨q, hq⟩
    rw [mem_filter, mem_primesBelow] at hq
    rcases hq with ⟨hq_prime_bound, hq_cond⟩
    have hq_prime := hq_prime_bound.2
    have hq_ge_2 : 2 ≤ q := hq_prime.two_le
    
    dsimp only at hq_cond
    by_cases hn_odd : (m / 2) % 2 = 1
    · have h_if : (if (m / 2) % 2 = 1 then 1 else 2) = 1 := by rw [if_pos hn_odd]
      rw [h_if] at hq_cond
      rcases hq_cond with ⟨hk_lt2, hp_prime, hp'_prime⟩
      use m / 2 - (q * 1 - 1), m / 2 + (q * 1 - 1)
      refine ⟨hp_prime, hp'_prime, ?_⟩
      omega
    · have h_if : (if (m / 2) % 2 = 1 then 1 else 2) = 2 := by rw [if_neg hn_odd]
      rw [h_if] at hq_cond
      rcases hq_cond with ⟨hk_lt2, hp_prime, hp'_prime⟩
      use m / 2 - (q * 2 - 1), m / 2 + (q * 2 - 1)
      refine ⟨hp_prime, hp'_prime, ?_⟩
      omega

lemma lemoine_from_A26 (h : A261627_conjecture) : lemoine_conjecture := by
  intro m hm
  rcases hm with ⟨hm7, hm_odd⟩
  rcases eq_or_lt_of_le hm7 with rfl | hm9
  · use 3, 2
    norm_num
  · have h_n : 6 < m - 1 := by omega
    have h_a26 := h (m - 1) h_n
    unfold A261627 at h_a26
    have h_pos : 0 < (filter (fun p =>
      let k := p * (if (m - 1) % 2 = 1 then 1 else 2) - 1
      k < m - 1 ∧ (m - 1 - k).Prime ∧ (m - 1 + k).Prime) (primesBelow (m - 1 + 1))).card := h_a26
    rw [Finset.card_pos] at h_pos
    rcases h_pos with ⟨q, hq⟩
    rw [mem_filter, mem_primesBelow] at hq
    rcases hq with ⟨hq_prime_bound, hq_cond⟩
    have hq_prime := hq_prime_bound.2
    have hm_even : (m - 1) % 2 = 0 := by
      rcases hm_odd with ⟨c, hc⟩
      rw [hc]
      omega
    have h_if : (if (m - 1) % 2 = 1 then 1 else 2) = 2 := by
      rw [if_neg]
      omega
    dsimp only at hq_cond
    rw [h_if] at hq_cond
    rcases hq_cond with ⟨hk_lt, hp_prime, hp'_prime⟩
    have hk_eq : q * 2 - 1 < m - 1 := hk_lt
    use m - 1 - (q * 2 - 1), q
    refine ⟨hp_prime, hq_prime, ?_⟩
    have hq_ge_2 : 2 ≤ q := hq_prime.two_le
    omega

theorem oeis_261627_conjecture_1 : A261627_conjecture → goldbach_conjecture ∧ lemoine_conjecture := by
  intro h
  exact ⟨goldbach_from_A26 h, lemoine_from_A26 h⟩

theorem oeis_261627_conjecture_1.disproof : ¬ (type_of% @oeis_261627_conjecture_1) := sorry
