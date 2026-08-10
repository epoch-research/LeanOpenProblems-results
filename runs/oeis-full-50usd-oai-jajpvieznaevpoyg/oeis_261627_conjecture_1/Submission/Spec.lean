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
  intro hA
  constructor
  · -- Goldbach: apply the A261627 conjecture to the midpoint of the even number.
    intro m hm
    rcases hm with ⟨hm4, hmEven⟩
    rcases hmEven with ⟨N, rfl⟩
    by_cases hN : 6 < N
    · have hpos : 0 < A261627 N := hA N hN
      unfold A261627 at hpos
      rcases Finset.card_pos.mp hpos with ⟨p, hpfilter⟩
      simp only [Finset.mem_filter] at hpfilter
      rcases hpfilter with ⟨_hpMem, hcond⟩
      rcases hcond with ⟨hklt, hleft, hright⟩
      let k : ℕ := p * (if N % 2 = 1 then 1 else 2) - 1
      change k < N at hklt
      change Nat.Prime (N - k) at hleft
      change Nat.Prime (N + k) at hright
      exact ⟨N - k, N + k, hleft, hright, by omega⟩
    · have hNle : N ≤ 6 := by omega
      interval_cases N
      · omega
      · omega
      · exact ⟨2, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, 5, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨5, 5, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨5, 7, by norm_num, by norm_num, by norm_num⟩
  · -- Lemoine: for odd n > 7 apply A261627 to the even number n - 1.
    intro n hn
    rcases hn with ⟨hn7, hnOdd⟩
    by_cases hn_eq : n = 7
    · subst n
      exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
    · have hn_gt : 7 < n := by omega
      have hcenter : 6 < n - 1 := by omega
      have hmod : (n - 1) % 2 ≠ 1 := by
        rcases hnOdd with ⟨t, ht⟩
        subst n
        simp
      have hpos : 0 < A261627 (n - 1) := hA (n - 1) hcenter
      unfold A261627 at hpos
      simp [hmod] at hpos
      rcases hpos with ⟨p, hpfilter⟩
      simp only [Finset.mem_filter] at hpfilter
      rcases hpfilter with ⟨hpMem, hcond⟩
      rcases hcond with ⟨hklt, hleft, _hright⟩
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primesBelow hpMem
      exact ⟨n - 1 - (p * 2 - 1), p, hleft, hpprime, by
        have hp0 : 0 < p := hpprime.pos
        omega⟩
