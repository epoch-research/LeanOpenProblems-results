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

/-- If `n` is odd, the only prime `q` that can make `n - q` and `n + q` prime is `q = 2`
(any odd prime `q` would make `n + q` an even number, hence `= 2`, impossible as `q ≥ 3`).
So `a n ≤ 1`. -/
theorem a_odd_le (n : ℕ) (hodd : ¬ Even n) : a n ≤ 1 := by
  unfold a
  have hsub : (Finset.filter (fun q : ℕ =>
      Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n))
      ⊆ {2} := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqlt, hqp, hnq, hnq2⟩ := hq
    simp only [Finset.mem_singleton]
    by_contra hne
    have hqodd : ¬ Even q := by
      rw [Nat.Prime.even_iff hqp]; exact hne
    have : Even (n + q) := by
      rw [Nat.even_add]
      constructor
      · intro h; exact absurd h hodd
      · intro h; exact absurd h hqodd
    have h2 : n + q = 2 := (Nat.Prime.even_iff hnq2).mp this
    have hq2 : 2 ≤ q := hqp.two_le
    omega
  calc a n = _ := rfl
  _ ≤ ({2} : Finset ℕ).card := Finset.card_le_card hsub
  _ = 1 := by simp

/-- If `n` is even but not divisible by `3`, then for any prime `q ≠ 3` exactly one of
`n - q`, `n`, `n + q` is divisible by `3`; since `3 ∤ n` and `n + q` is too large to equal `3`,
we must have `n - q = 3`, i.e. `q = n - 3`. Hence every solution lies in `{3, n - 3}` and
`a n ≤ 2`. -/
theorem a_even_not3_le (n : ℕ) (h3 : ¬ (3 ∣ n)) : a n ≤ 2 := by
  unfold a
  have hsub : (Finset.filter (fun q : ℕ =>
      Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n))
      ⊆ {3, n - 3} := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqlt, hqp, hnq, hnq2⟩ := hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    obtain ⟨hne3, hnen3⟩ := hne
    have hq3 : ¬ (3 ∣ q) := by
      intro hdvd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hqp 3 hdvd) with h | h
      · norm_num at h
      · exact hne3 h.symm
    have hnm : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hqm : q % 3 = 1 ∨ q % 3 = 2 := by omega
    have hdvd : 3 ∣ (n - q) ∨ 3 ∣ (n + q) := by
      rcases hnm with h | h <;> rcases hqm with h' | h' <;> omega
    rcases hdvd with hd | hd
    · have : n - q = 3 := by
        rcases (Nat.Prime.eq_one_or_self_of_dvd hnq 3 hd) with h | h
        · norm_num at h
        · exact h.symm
      have : q = n - 3 := by omega
      exact hnen3 this
    · have : n + q = 3 := by
        rcases (Nat.Prime.eq_one_or_self_of_dvd hnq2 3 hd) with h | h
        · norm_num at h
        · exact h.symm
      have hq2 : 2 ≤ q := hqp.two_le
      omega
  calc a n = _ := rfl
  _ ≤ ({3, n - 3} : Finset ℕ).card := Finset.card_le_card hsub
  _ ≤ 2 := by
    apply le_trans (Finset.card_insert_le _ _)
    simp

/-- Reduction: `a n = 4` forces `6 ∣ n`. -/
theorem a_eq_four_dvd_six (n : ℕ) (hn : a n = 4) : 6 ∣ n := by
  have heven : Even n := by
    by_contra h; have := a_odd_le n h; omega
  have h3 : 3 ∣ n := by
    by_contra h; have := a_even_not3_le n h; omega
  obtain ⟨k, hk⟩ := heven
  obtain ⟨m, hm⟩ := h3
  omega

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  have h6 : 6 ∣ n := a_eq_four_dvd_six n hn
  obtain ⟨k, rfl⟩ := h6
  rcases Nat.lt_or_ge k 4 with hk | hk
  · -- Small cases n ∈ {0, 6, 12, 18}: a n = 0, 0, 2, 3 respectively, all ≠ 4.
    interval_cases k <;> exact absurd hn (by decide)
  · -- Open core: n = 6 * k with k ≥ 4, i.e. n ≥ 24.
    -- Requires a n ≥ 5 for all multiples of 6 that are ≥ 24, a statement about the
    -- existence of ≥ 5 primes q with n - q and n + q both prime.  This is a lower
    -- bound on the number of prime triples (n - q, q, n + q); it is strictly stronger
    -- than Goldbach's conjecture and is currently open.
    sorry
