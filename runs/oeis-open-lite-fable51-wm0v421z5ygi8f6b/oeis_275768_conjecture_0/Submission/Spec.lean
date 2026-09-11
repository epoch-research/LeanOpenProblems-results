import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275768: $a(n)$ is the number of ways to express $n = \frac{\operatorname{prime}(i) + \operatorname{prime}(j)}{2}$ when $\frac{|\operatorname{prime}(i) - \operatorname{prime}(j)|}{2}$ also is prime.
This is equivalent to counting the number of primes $q$ such that $n - q$ and $n + q$ are also prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

/-! ### Elementary reduction: only multiples of 6 matter

If `n` is odd, then for an odd prime `q` the number `n + q ≥ 3` is even, hence not prime,
so only `q = 2` can contribute and `a n ≤ 1`.

If `n` is even but `3 ∤ n`, then for a prime `q ≠ 3` one of `n - q`, `n + q` is divisible
by `3`, hence must equal `3`; `n + q = 3` is impossible, so `q = n - 3`.  Thus only
`q ∈ {3, n - 3}` can contribute and `a n ≤ 2`.

Consequently `a n = 4` can only happen when `6 ∣ n`.
-/

/-- If `n` is odd, only `q = 2` can contribute. -/
lemma a_le_one_of_odd (n : ℕ) (hn : ¬ 2 ∣ n) : a n ≤ 1 := by
  unfold a
  calc (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q))
          (Finset.range n)).card
      ≤ ({2} : Finset ℕ).card := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq
        obtain ⟨hqn, hq, _, hnq⟩ := hq
        simp only [Finset.mem_singleton]
        rcases hq.eq_two_or_odd' with h | h
        · exact h
        · exfalso
          have h2 : 2 ∣ n + q := by
            rcases h with ⟨k, hk⟩
            omega
          have := (Nat.Prime.eq_one_or_self_of_dvd hnq 2 h2)
          have := hq.two_le
          omega
    _ = 1 := by simp

/-- If `3 ∤ n`, only `q = 3` and `q = n - 3` can contribute. -/
lemma a_le_two_of_not_three_dvd (n : ℕ) (hn : ¬ 3 ∣ n) : a n ≤ 2 := by
  unfold a
  calc (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q))
          (Finset.range n)).card
      ≤ ({3, n - 3} : Finset ℕ).card := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq
        obtain ⟨hqn, hq, hnq', hnq⟩ := hq
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h3 : q = 3
        · exact Or.inl h3
        · right
          have h3q : ¬ 3 ∣ q := by
            intro hd
            have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 hd)
            omega
          have h2 := hq.two_le
          -- one of n - q, n + q is divisible by 3
          have key : 3 ∣ n - q ∨ 3 ∣ n + q := by
            have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by omega
            have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by omega
            rcases hn3 with hn3 | hn3 <;> rcases hq3 with hq3 | hq3
            · left; omega
            · right; omega
            · right; omega
            · left; omega
          rcases key with hd | hd
          · have := Nat.Prime.eq_one_or_self_of_dvd hnq' 3 hd
            omega
          · have := Nat.Prime.eq_one_or_self_of_dvd hnq 3 hd
            omega
    _ ≤ 2 := Finset.card_le_two

lemma a_le_two_of_not_six_dvd (n : ℕ) (hn : ¬ 6 ∣ n) : a n ≤ 2 := by
  by_cases h2 : 2 ∣ n
  · by_cases h3 : 3 ∣ n
    · exact absurd (by omega) hn
    · exact a_le_two_of_not_three_dvd n h3
  · exact (a_le_one_of_odd n h2).trans (by norm_num)

set_option maxRecDepth 100000 in
/-- Finite verification for small `n` (kernel computation). -/
lemma a_ne_four_of_lt_200 : ∀ n ∈ Finset.range 200, a n ≠ 4 := by
  decide +kernel

/-
### The remaining case `6 ∣ n`, `n ≥ 200`

This is the genuinely open part.  Numerically, `a n ≥ 5` for every multiple of `6` with
`200 < n ≤ 4·10^8`, and `a n` grows like `n / (log n)^3` times a singular series that is
bounded below, so `a n = 4` never occurs.  However, showing `a n ≠ 4` for all large multiples
of `6` requires a *lower bound* `a n ≥ 5`, i.e. at least five prime triples
`(q, n - q, n + q)`; even `a n ≥ 1` would give a Goldbach representation
`2n = (n - q) + (n + q)`.  This is strictly stronger than the binary Goldbach conjecture for
multiples of `12`, which is beyond all currently available methods (sieve theory and the
circle method give no lower bounds for such "binary" problems for every `n`).
-/

/-- The conjecture follows from the Goldbach-strength lower bound `a n ≥ 5` for all
multiples of `6` with `n ≥ 200` (which is numerically true up to `4·10^8`). -/
theorem oeis_275768_of_lower_bound
    (H : ∀ n : ℕ, 6 ∣ n → 200 ≤ n → 5 ≤ a n) : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  by_cases h6 : 6 ∣ n
  · by_cases hlt : n < 200
    · exact a_ne_four_of_lt_200 n (Finset.mem_range.mpr hlt) hn
    · have := H n h6 (by omega)
      omega
  · have := a_le_two_of_not_six_dvd n h6
    omega

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  apply oeis_275768_of_lower_bound
  -- Open: a lower bound of Goldbach strength (stronger than binary Goldbach for `12 ∣ 2n`).
  sorry

theorem oeis_275768_conjecture_0.disproof : ¬ (type_of% @oeis_275768_conjecture_0) := sorry
