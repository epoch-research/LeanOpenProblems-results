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
theorem oeis_261627_conjecture_1 : A261627_conjecture → goldbach_conjecture ∧ lemoine_conjecture := by
  intro h
  -- extraction helper
  have key : ∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧
      (p * (if n % 2 = 1 then 1 else 2) - 1) < n ∧
      Nat.Prime (n - (p * (if n % 2 = 1 then 1 else 2) - 1)) ∧
      Nat.Prime (n + (p * (if n % 2 = 1 then 1 else 2) - 1)) := by
    intro n hn
    have hpos := h n hn
    unfold A261627 at hpos
    rw [Finset.card_pos] at hpos
    obtain ⟨p, hp⟩ := hpos
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    exact ⟨p, prime_of_mem_primesBelow hp1, hp2, hp3, hp4⟩
  constructor
  · -- Goldbach
    rintro m ⟨hm4, hmeven⟩
    have hmmod : m % 2 = 0 := Nat.even_iff.mp hmeven
    by_cases hbig : 6 < m / 2
    · obtain ⟨p, hpp, hk, hlo, hhi⟩ := key (m / 2) hbig
      set k := p * (if (m/2) % 2 = 1 then 1 else 2) - 1 with hkdef
      refine ⟨m / 2 - k, m / 2 + k, hlo, hhi, ?_⟩
      omega
    · -- small even m: m ∈ {4,6,8,10,12}
      have hub : m ≤ 13 := by omega
      interval_cases m
      · exact ⟨2, 2, by norm_num, by norm_num, by norm_num⟩
      · exfalso; omega
      · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
      · exfalso; omega
      · exact ⟨3, 5, by norm_num, by norm_num, by norm_num⟩
      · exfalso; omega
      · exact ⟨5, 5, by norm_num, by norm_num, by norm_num⟩
      · exfalso; omega
      · exact ⟨5, 7, by norm_num, by norm_num, by norm_num⟩
      · exfalso; omega
  · -- Lemoine
    rintro N ⟨hN7, hNodd⟩
    rcases eq_or_lt_of_le hN7 with hN | hN
    · -- N = 7
      exact ⟨3, 2, by norm_num, by norm_num, by omega⟩
    · -- N ≥ 8, and N odd so N ≥ 9
      have hNge9 : 9 ≤ N := by
        rcases hNodd with ⟨t, ht⟩; omega
      set n := N - 1 with hndef
      have hnbig : 6 < n := by omega
      have hneven : n % 2 = 0 := by
        rcases hNodd with ⟨t, ht⟩; omega
      have hif : (if n % 2 = 1 then 1 else 2) = 2 := by
        rw [if_neg]; omega
      obtain ⟨p, hpp, hk, hlo, hhi⟩ := key n hnbig
      rw [hif] at hk hlo hhi
      have hp2 : 2 ≤ p := hpp.two_le
      refine ⟨n - (p * 2 - 1), p, hlo, hpp, ?_⟩
      omega
