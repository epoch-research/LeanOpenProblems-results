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

/-- Structural lemma. If `n` is not divisible by `6`, then every prime `q < n`
that is counted by `a` (i.e. with `n - q` and `n + q` also prime) must be one of
`2`, `3`, or `n - 3`.

Reason:
* If `n` is odd then any odd prime `q` makes `n + q` even and `> 2`, hence composite;
  so the only possibility is `q = 2`.
* If `3 ∤ n` then, since one of `q, n - q, n + q` is always divisible by `3`,
  primality forces that one to equal `3`; as `n + q > 3`, this means `q = 3`
  or `n - q = 3` (i.e. `q = n - 3`). -/
lemma rep_mem_of_not_six_dvd (n q : ℕ) (h6 : ¬ (6 ∣ n))
    (hlt : q < n) (hq : Nat.Prime q) (hnq : Nat.Prime (n - q)) (hnq2 : Nat.Prime (n + q)) :
    q = 2 ∨ q = 3 ∨ q = n - 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hq2, hq3, hq3'⟩ := hcon
  have h2le : 2 ≤ q := hq.two_le
  -- `q` is odd: `¬ 2 ∣ q`
  have hqodd : ¬ (2 ∣ q) := by
    intro hd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq 2 hd) with h | h
    · simp at h
    · exact hq2 h.symm
  -- `3 ∤ q`
  have hq3dvd : ¬ (3 ∣ q) := by
    intro hd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq 3 hd) with h | h
    · simp at h
    · exact hq3 h.symm
  -- hence `q ≥ 5`
  have hq5 : 5 ≤ q := by omega
  -- `¬ 6 ∣ n` splits into `¬ 2 ∣ n` or `¬ 3 ∣ n`
  have hdisj : ¬ (2 ∣ n) ∨ ¬ (3 ∣ n) := by
    by_contra hc
    push_neg at hc
    exact h6 (by omega)
  rcases hdisj with hn2 | hn3
  · -- `n` odd, `q` odd ⟹ `n + q` even and `> 2` ⟹ not prime
    have : 2 ∣ (n + q) := by omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hnq2 2 this) with h | h
    · simp at h
    · omega
  · -- `3 ∤ n` and `3 ∤ q` ⟹ `3 ∣ (n - q)` or `3 ∣ (n + q)`
    have hnr : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hqr : q % 3 = 1 ∨ q % 3 = 2 := by omega
    have hmod : 3 ∣ (n - q) ∨ 3 ∣ (n + q) := by omega
    rcases hmod with hd | hd
    · -- `n - q` prime and divisible by `3` ⟹ `n - q = 3` ⟹ `q = n - 3`
      rcases (Nat.Prime.eq_one_or_self_of_dvd hnq 3 hd) with h | h
      · simp at h
      · omega
    · -- `n + q` prime and divisible by `3` ⟹ `n + q = 3`, impossible
      rcases (Nat.Prime.eq_one_or_self_of_dvd hnq2 3 hd) with h | h
      · simp at h
      · omega

/-- For `n` not divisible by `6`, the count `a n` is at most `3` (in fact at most `2`),
because every counted `q` lies in the three-element set `{2, 3, n - 3}`. -/
lemma a_le_three (n : ℕ) (h6 : ¬ (6 ∣ n)) : a n ≤ 3 := by
  unfold a
  have hsub : Finset.filter (fun q : ℕ =>
      Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n)
      ⊆ ({2, 3, n - 3} : Finset ℕ) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hlt, hp1, hp2, hp3⟩ := hq
    have := rep_mem_of_not_six_dvd n q h6 hlt hp1 hp2 hp3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  calc Finset.card _ ≤ ({2, 3, n - 3} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
        simp [Finset.card_singleton]

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  by_cases h6 : 6 ∣ n
  · obtain ⟨m, rfl⟩ := h6
    rcases lt_or_ge m 4 with hm | hm
    · -- `n = 6 * m` with `m < 4`, i.e. `n ∈ {0, 6, 12, 18}`: direct computation.
      interval_cases m <;> revert hn <;> native_decide
    · -- `n = 6 * m` with `m ≥ 4`, i.e. `n ≥ 24`: requires the (open) bound `a n ≥ 5`.
      sorry
  · -- `6 ∤ n`: `a n ≤ 3 < 4`.
    have := a_le_three n h6
    omega
