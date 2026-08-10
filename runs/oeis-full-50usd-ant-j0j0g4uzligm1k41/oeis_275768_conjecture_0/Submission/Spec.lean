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

/-- If `n` is odd then `a n ≤ 1`: the only prime `q` for which `n - q` and `n + q`
can both be prime is `q = 2` (for odd `q` both `n ± q` are even and `> 2`). -/
theorem a_le_one_of_odd (n : ℕ) (hn : Odd n) : a n ≤ 1 := by
  unfold a
  apply le_trans (Finset.card_le_card (s := _) (t := {2}) ?_)
  · simp
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqn, hqp, hnq, hnpq⟩ := hq
    simp only [Finset.mem_singleton]
    by_contra hne
    have hqodd : Odd q := hqp.odd_of_ne_two hne
    have hq2 : 2 ≤ q := hqp.two_le
    have : Even (n + q) := hn.add_odd hqodd
    have h2 : n + q = 2 := (hnpq.even_iff).mp this
    omega

/-- If `n` is even and not divisible by `3` then `a n ≤ 2`: the only candidates are
`q = 3` and `q = n - 3` (any other prime `q` makes one of `n ± q` a multiple of `3`
that is `> 3`, hence composite; and `q = 2` makes `n ± q` even and `> 2`). -/
theorem a_le_two_of_not_dvd_three (n : ℕ) (hn : Even n) (h3 : ¬ (3 ∣ n)) : a n ≤ 2 := by
  unfold a
  apply le_trans (Finset.card_le_card (s := _) (t := {3, n - 3}) ?_)
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqn, hqp, hnq, hnpq⟩ := hq
    have hq2 : 2 ≤ q := hqp.two_le
    have hqne2 : q ≠ 2 := by
      rintro rfl
      have : Even (n + 2) := by
        obtain ⟨k, rfl⟩ := hn; exact ⟨k+1, by ring⟩
      have := (hnpq.even_iff).mp this
      omega
    by_cases hq3 : q = 3
    · subst hq3; simp
    · have h3q : ¬ (3 ∣ q) := by
        intro hd
        exact hq3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hqp).mp hd).symm
      have hqlt : q ≤ n := le_of_lt hqn
      have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by omega
      have hq3' : q % 3 = 1 ∨ q % 3 = 2 := by omega
      have hmod : (3 ∣ (n - q)) ∨ (3 ∣ (n + q)) := by
        rcases hn3 with h | h <;> rcases hq3' with h' | h' <;> omega
      rcases hmod with hd | hd
      · have h33 : (3 : ℕ) = n - q := by
          rcases (hnq.eq_one_or_self_of_dvd 3 hd) with h | h
          · omega
          · exact h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right; omega
      · exfalso
        have : (3 : ℕ) = n + q := by
          rcases (hnpq.eq_one_or_self_of_dvd 3 hd) with h | h
          · omega
          · exact h
        omega

/-- Reduction step: if `a n = 4` then `6 ∣ n`.  Indeed `a n ≤ 1` for odd `n` and
`a n ≤ 2` for even `n` not divisible by `3`, so `a n = 4` forces `n` to be even and
divisible by `3`, i.e. `6 ∣ n`. -/
theorem dvd_six_of_a_eq_four (n : ℕ) (h : a n = 4) : 6 ∣ n := by
  rcases Nat.even_or_odd n with he | ho
  · by_cases h3 : 3 ∣ n
    · obtain ⟨k, rfl⟩ := he
      omega
    · have := a_le_two_of_not_dvd_three n he h3
      omega
  · have := a_le_one_of_odd n ho
    omega

/-- The residual core of the conjecture, isolated: for `n ≡ 0 (mod 6)` with `n ≥ 24`
one has `a n ≠ 4` (in fact `a n ≥ 5`).

This is the genuinely hard part of Zhi-Wei Sun's conjecture (OEIS A275768).  It has
been verified computationally (no `n ≤ 10⁸` gives `a n < 5` once `n ≥ 24`), and the
count `a n` grows without bound.  However a proof is out of reach of current methods:
already `a n ≥ 1` for `n ≡ 0 (mod 6)` means `n = q + (n - q)` is a sum of two primes,
so establishing `a n ≥ 5` for all such `n` would prove binary Goldbach for every
multiple of `6` that is `≥ 24`.  Moreover `a n` attains every value `≥ 5` and is
unbounded in each residue class, so no purely modular/parity argument can exclude the
value `4` either. -/
theorem a_ne_four_of_dvd_six_ge (n : ℕ) (h6 : 6 ∣ n) (hge : 24 ≤ n) : a n ≠ 4 := by
  sorry

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  -- By `dvd_six_of_a_eq_four`, any counterexample `n` satisfies `6 ∣ n`.
  have h6 : 6 ∣ n := dvd_six_of_a_eq_four n hn
  by_cases hlt : n < 24
  · -- Small cases `n ∈ {0, 6, 12, 18}`: direct kernel computation gives `a n ∈ {0,2,3}`.
    interval_cases n <;> first | omega | (revert hn; decide)
  · -- The open core.
    exact a_ne_four_of_dvd_six_ge n h6 (by omega) hn
