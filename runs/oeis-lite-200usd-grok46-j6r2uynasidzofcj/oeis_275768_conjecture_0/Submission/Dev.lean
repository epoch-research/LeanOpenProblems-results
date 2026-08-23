import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def Sset (n : ℕ) : Finset ℕ :=
  Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n)

lemma a_eq_card_Sset (n : ℕ) : a n = #(Sset n) := rfl

lemma mem_Sset_iff {n q : ℕ} :
    q ∈ Sset n ↔ q < n ∧ q.Prime ∧ (n - q).Prime ∧ (n + q).Prime := by
  simp [Sset, mem_filter, mem_range]

/-- An even natural number other than 2 is not prime. -/
lemma not_prime_of_even_of_ne_two {m : ℕ} (he : Even m) (hne : m ≠ 2) : ¬ m.Prime :=
  fun hp => hne (hp.even_iff.mp he)

/-- For odd `n`, every element of `Sset n` equals `2`. -/
lemma eq_two_of_mem_Sset_of_odd {n q : ℕ} (hn : Odd n) (hq : q ∈ Sset n) : q = 2 := by
  have h := mem_Sset_iff.mp hq
  have hqP : q.Prime := h.2.1
  have hsumP : (n + q).Prime := h.2.2.2
  by_contra hne
  have hqOdd : Odd q := hqP.odd_of_ne_two hne
  have heven : Even (n + q) := Odd.add_odd hn hqOdd
  have hne2 : n + q ≠ 2 := by
    have hq2 : 2 ≤ q := hqP.two_le
    have hn1 : 1 ≤ n := hn.pos
    omega
  exact not_prime_of_even_of_ne_two heven hne2 hsumP

lemma Sset_odd_subset_singleton_two {n : ℕ} (hn : Odd n) : Sset n ⊆ {2} := by
  intro q hq
  simp [eq_two_of_mem_Sset_of_odd hn hq]

lemma a_le_one_of_odd {n : ℕ} (hn : Odd n) : a n ≤ 1 := by
  rw [a_eq_card_Sset]
  exact (card_le_card (Sset_odd_subset_singleton_two hn)).trans (by simp)

lemma a_ne_four_of_odd {n : ℕ} (hn : Odd n) : a n ≠ 4 := by
  have : a n ≤ 1 := a_le_one_of_odd hn
  omega

/-- A prime other than 3 is not divisible by 3, hence is 1 or 2 modulo 3. -/
lemma prime_mod_three_eq_one_or_two {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have h : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h with h0 | h12
  · have hdvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.2 h0
    have heq : 3 = p := (prime_dvd_prime_iff_eq prime_three hp).mp hdvd
    exact (h3 heq.symm).elim
  · exact h12

lemma six_dvd_of_two_dvd_of_three_dvd {n : ℕ} (h2 : 2 ∣ n) (h3 : 3 ∣ n) : 6 ∣ n := by
  have : Nat.lcm 2 3 ∣ n := Nat.lcm_dvd h2 h3
  simpa [show Nat.lcm 2 3 = 6 by decide] using this

/-- For even `n` not divisible by 3, every `q ∈ Sset n` is `3` or `n - 3`. -/
lemma mem_Sset_of_even_of_not_dvd_three {n q : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n)
    (hq : q ∈ Sset n) : q = 3 ∨ q = n - 3 := by
  have h := mem_Sset_iff.mp hq
  have hqlt : q < n := h.1
  have hqP : q.Prime := h.2.1
  have hdiffP : (n - q).Prime := h.2.2.1
  have hsumP : (n + q).Prime := h.2.2.2
  have hq_ne2 : q ≠ 2 := by
    intro hq2
    subst hq2
    have heven_sum : Even (n + 2) := hn.add even_two
    have hne2 : n + 2 ≠ 2 := by omega
    exact not_prime_of_even_of_ne_two heven_sum hne2 hsumP
  by_cases hq3 : q = 3
  · exact Or.inl hq3
  · have hq_mod : q % 3 = 1 ∨ q % 3 = 2 := prime_mod_three_eq_one_or_two hqP hq3
    have hn_mod : n % 3 = 1 ∨ n % 3 = 2 := by
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with h0 | h12
      · exact (h3 (Nat.dvd_iff_mod_eq_zero.2 h0)).elim
      · exact h12
    have hsum_or_diff : (n + q) % 3 = 0 ∨ (n - q) % 3 = 0 := by
      rcases hn_mod with hn1 | hn2
      · rcases hq_mod with hq1 | hq2
        · right
          exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
        · left
          omega
      · rcases hq_mod with hq1 | hq2
        · left
          omega
        · right
          exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
    rcases hsum_or_diff with hsum0 | hdiff0
    · have hdvd : 3 ∣ n + q := Nat.dvd_iff_mod_eq_zero.2 hsum0
      have hgt : 3 < n + q := by
        have : 5 ≤ q := hqP.five_le_of_ne_two_of_ne_three hq_ne2 hq3
        omega
      exact absurd hsumP (not_prime_of_dvd_of_lt hdvd (by norm_num) hgt)
    · have hdvd : 3 ∣ n - q := Nat.dvd_iff_mod_eq_zero.2 hdiff0
      have hnqe : n - q = 3 := by
        by_contra hne
        have hge : 2 ≤ n - q := hdiffP.two_le
        have hcases : n - q < 3 ∨ 3 < n - q := by omega
        rcases hcases with hlt | hgt
        · have : n - q = 2 := by omega
          exact (by decide : ¬ 3 ∣ (2 : ℕ)) (this ▸ hdvd)
        · exact not_prime_of_dvd_of_lt hdvd (by norm_num) hgt hdiffP
      have : q = n - 3 := by omega
      exact Or.inr this

lemma Sset_subset_pair_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    Sset n ⊆ {3, n - 3} := by
  intro q hq
  rcases mem_Sset_of_even_of_not_dvd_three hn h3 hq with h | h
  · simp [h]
  · simp [h]

lemma a_le_two_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    a n ≤ 2 := by
  rw [a_eq_card_Sset]
  refine (card_le_card (Sset_subset_pair_of_even_of_not_dvd_three hn h3)).trans ?_
  apply (card_insert_le _ _).trans
  simp

lemma a_ne_four_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    a n ≠ 4 := by
  have : a n ≤ 2 := a_le_two_of_even_of_not_dvd_three hn h3
  omega

/-- If `n` is not divisible by 6 then `a n ≠ 4`. -/
lemma a_ne_four_of_not_dvd_six {n : ℕ} (h : ¬ 6 ∣ n) : a n ≠ 4 := by
  by_cases hn2 : Even n
  · have h3 : ¬ 3 ∣ n := fun h3 =>
      h (six_dvd_of_two_dvd_of_three_dvd (even_iff_two_dvd.mp hn2) h3)
    exact a_ne_four_of_even_of_not_dvd_three hn2 h3
  · exact a_ne_four_of_odd (Nat.not_even_iff_odd.mp hn2)

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Direct check that `a n ≠ 4` for all `n < 80`. -/
lemma a_ne_four_of_lt_eighty {n : ℕ} (hn : n < 80) : a n ≠ 4 := by
  revert n
  decide

/-- If `6 ∣ n` and `n < 80` then `a n ≠ 4`. -/
lemma a_ne_four_of_dvd_six_of_lt_eighty {n : ℕ} (h6 : 6 ∣ n) (hn : n < 80) : a n ≠ 4 :=
  a_ne_four_of_lt_eighty hn

theorem oeis_275768_conjecture_0_aux : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  by_cases h6 : 6 ∣ n
  · by_cases hlt : n < 80
    · exact a_ne_four_of_lt_eighty hlt hn
    · -- n ≥ 80 and 6 ∣ n : remaining case
      have hge : 80 ≤ n := Nat.le_of_not_gt hlt
      -- TODO: prove a n ≥ 5
      sorry
  · exact a_ne_four_of_not_dvd_six h6 hn
