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


set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma mem_Sset_of_primes {n q : ℕ}
    (h1 : q < n) (h2 : q.Prime) (h3 : (n - q).Prime) (h4 : (n + q).Prime) :
    q ∈ Sset n := mem_Sset_iff.mpr ⟨h1, h2, h3, h4⟩

lemma five_le_a_of_five_mem {n q1 q2 q3 q4 q5 : ℕ}
    (h1 : q1 ∈ Sset n) (h2 : q2 ∈ Sset n) (h3 : q3 ∈ Sset n)
    (h4 : q4 ∈ Sset n) (h5 : q5 ∈ Sset n)
    (hne : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q1 ≠ q4 ∧ q1 ≠ q5 ∧
           q2 ≠ q3 ∧ q2 ≠ q4 ∧ q2 ≠ q5 ∧
           q3 ≠ q4 ∧ q3 ≠ q5 ∧ q4 ≠ q5) :
    5 ≤ a n := by
  rw [a_eq_card_Sset]
  have hs : ({q1, q2, q3, q4, q5} : Finset ℕ) ⊆ Sset n := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  have hc : 5 ≤ #({q1, q2, q3, q4, q5} : Finset ℕ) := by
    repeat first | rw [card_insert_of_notMem] | rw [card_singleton]
    · simp [hne]
    all_goals simp [hne]
  exact hc.trans (card_le_card hs)

macro "prove_in_Sset" : tactic => `(tactic|
  apply mem_Sset_of_primes <;> norm_num)


lemma five_le_a_24 : 5 ≤ a 24 :=
  five_le_a_of_five_mem (n := 24) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 17) (q5 := 19)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_30 : 5 ≤ a 30 :=
  five_le_a_of_five_mem (n := 30) (q1 := 7) (q2 := 11) (q3 := 13) (q4 := 17) (q5 := 23)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_36 : 5 ≤ a 36 :=
  five_le_a_of_five_mem (n := 36) (q1 := 5) (q2 := 7) (q3 := 17) (q4 := 23) (q5 := 31)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_42 : 5 ≤ a 42 :=
  five_le_a_of_five_mem (n := 42) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 29) (q5 := 31)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_48 : 5 ≤ a 48 :=
  five_le_a_of_five_mem (n := 48) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 31) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_54 : 5 ≤ a 54 :=
  five_le_a_of_five_mem (n := 54) (q1 := 7) (q2 := 13) (q3 := 17) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_60 : 5 ≤ a 60 :=
  five_le_a_of_five_mem (n := 60) (q1 := 7) (q2 := 13) (q3 := 19) (q4 := 23) (q5 := 29)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_66 : 5 ≤ a 66 :=
  five_le_a_of_five_mem (n := 66) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 23) (q5 := 37)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_72 : 5 ≤ a 72 :=
  five_le_a_of_five_mem (n := 72) (q1 := 11) (q2 := 29) (q3 := 31) (q4 := 41) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_78 : 5 ≤ a 78 :=
  five_le_a_of_five_mem (n := 78) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 31) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_84 : 5 ≤ a 84 :=
  five_le_a_of_five_mem (n := 84) (q1 := 5) (q2 := 13) (q3 := 17) (q4 := 23) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_90 : 5 ≤ a 90 :=
  five_le_a_of_five_mem (n := 90) (q1 := 7) (q2 := 11) (q3 := 17) (q4 := 19) (q5 := 23)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_96 : 5 ≤ a 96 :=
  five_le_a_of_five_mem (n := 96) (q1 := 7) (q2 := 13) (q3 := 17) (q4 := 43) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_102 : 5 ≤ a 102 :=
  five_le_a_of_five_mem (n := 102) (q1 := 5) (q2 := 29) (q3 := 61) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_108 : 5 ≤ a 108 :=
  five_le_a_of_five_mem (n := 108) (q1 := 5) (q2 := 19) (q3 := 29) (q4 := 41) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_114 : 5 ≤ a 114 :=
  five_le_a_of_five_mem (n := 114) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 53) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_120 : 5 ≤ a 120 :=
  five_le_a_of_five_mem (n := 120) (q1 := 7) (q2 := 11) (q3 := 17) (q4 := 19) (q5 := 31)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_126 : 5 ≤ a 126 :=
  five_le_a_of_five_mem (n := 126) (q1 := 13) (q2 := 23) (q3 := 37) (q4 := 47) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_132 : 5 ≤ a 132 :=
  five_le_a_of_five_mem (n := 132) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 59) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_138 : 5 ≤ a 138 :=
  five_le_a_of_five_mem (n := 138) (q1 := 11) (q2 := 29) (q3 := 41) (q4 := 59) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_144 : 5 ≤ a 144 :=
  five_le_a_of_five_mem (n := 144) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 37) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_150 : 5 ≤ a 150 :=
  five_le_a_of_five_mem (n := 150) (q1 := 13) (q2 := 23) (q3 := 41) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_156 : 5 ≤ a 156 :=
  five_le_a_of_five_mem (n := 156) (q1 := 7) (q2 := 17) (q3 := 43) (q4 := 67) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_162 : 5 ≤ a 162 :=
  five_le_a_of_five_mem (n := 162) (q1 := 5) (q2 := 11) (q3 := 31) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_168 : 5 ≤ a 168 :=
  five_le_a_of_five_mem (n := 168) (q1 := 5) (q2 := 11) (q3 := 29) (q4 := 31) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_174 : 5 ≤ a 174 :=
  five_le_a_of_five_mem (n := 174) (q1 := 7) (q2 := 17) (q3 := 23) (q4 := 37) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_180 : 5 ≤ a 180 :=
  five_le_a_of_five_mem (n := 180) (q1 := 13) (q2 := 17) (q3 := 31) (q4 := 43) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_186 : 5 ≤ a 186 :=
  five_le_a_of_five_mem (n := 186) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 37) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_192 : 5 ≤ a 192 :=
  five_le_a_of_five_mem (n := 192) (q1 := 19) (q2 := 41) (q3 := 79) (q4 := 89) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_198 : 5 ≤ a 198 :=
  five_le_a_of_five_mem (n := 198) (q1 := 31) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_204 : 5 ≤ a 204 :=
  five_le_a_of_five_mem (n := 204) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 47) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_210 : 5 ≤ a 210 :=
  five_le_a_of_five_mem (n := 210) (q1 := 13) (q2 := 17) (q3 := 19) (q4 := 29) (q5 := 31)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_216 : 5 ≤ a 216 :=
  five_le_a_of_five_mem (n := 216) (q1 := 17) (q2 := 23) (q3 := 53) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_222 : 5 ≤ a 222 :=
  five_le_a_of_five_mem (n := 222) (q1 := 11) (q2 := 29) (q3 := 41) (q4 := 59) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_228 : 5 ≤ a 228 :=
  five_le_a_of_five_mem (n := 228) (q1 := 5) (q2 := 29) (q3 := 79) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_234 : 5 ≤ a 234 :=
  five_le_a_of_five_mem (n := 234) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 37) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_240 : 5 ≤ a 240 :=
  five_le_a_of_five_mem (n := 240) (q1 := 11) (q2 := 17) (q3 := 29) (q4 := 41) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_246 : 5 ≤ a 246 :=
  five_le_a_of_five_mem (n := 246) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_252 : 5 ≤ a 252 :=
  five_le_a_of_five_mem (n := 252) (q1 := 11) (q2 := 19) (q3 := 29) (q4 := 41) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_258 : 5 ≤ a 258 :=
  five_le_a_of_five_mem (n := 258) (q1 := 19) (q2 := 59) (q3 := 79) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_264 : 5 ≤ a 264 :=
  five_le_a_of_five_mem (n := 264) (q1 := 7) (q2 := 13) (q3 := 53) (q4 := 67) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_270 : 5 ≤ a 270 :=
  five_le_a_of_five_mem (n := 270) (q1 := 7) (q2 := 13) (q3 := 37) (q4 := 41) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_276 : 5 ≤ a 276 :=
  five_le_a_of_five_mem (n := 276) (q1 := 5) (q2 := 7) (q3 := 37) (q4 := 83) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_282 : 5 ≤ a 282 :=
  five_le_a_of_five_mem (n := 282) (q1 := 11) (q2 := 31) (q3 := 71) (q4 := 101) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_288 : 5 ≤ a 288 :=
  five_le_a_of_five_mem (n := 288) (q1 := 5) (q2 := 19) (q3 := 59) (q4 := 61) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_294 : 5 ≤ a 294 :=
  five_le_a_of_five_mem (n := 294) (q1 := 13) (q2 := 17) (q3 := 23) (q4 := 37) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_300 : 5 ≤ a 300 :=
  five_le_a_of_five_mem (n := 300) (q1 := 7) (q2 := 17) (q3 := 31) (q4 := 37) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_306 : 5 ≤ a 306 :=
  five_le_a_of_five_mem (n := 306) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 83) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_312 : 5 ≤ a 312 :=
  five_le_a_of_five_mem (n := 312) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 61) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_318 : 5 ≤ a 318 :=
  five_le_a_of_five_mem (n := 318) (q1 := 41) (q2 := 61) (q3 := 79) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_324 : 5 ≤ a 324 :=
  five_le_a_of_five_mem (n := 324) (q1 := 7) (q2 := 13) (q3 := 43) (q4 := 73) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_330 : 5 ≤ a 330 :=
  five_le_a_of_five_mem (n := 330) (q1 := 17) (q2 := 19) (q3 := 23) (q4 := 37) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_336 : 5 ≤ a 336 :=
  five_le_a_of_five_mem (n := 336) (q1 := 23) (q2 := 43) (q3 := 53) (q4 := 73) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_342 : 5 ≤ a 342 :=
  five_le_a_of_five_mem (n := 342) (q1 := 5) (q2 := 11) (q3 := 31) (q4 := 59) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_348 : 5 ≤ a 348 :=
  five_le_a_of_five_mem (n := 348) (q1 := 11) (q2 := 31) (q3 := 41) (q4 := 71) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_354 : 5 ≤ a 354 :=
  five_le_a_of_five_mem (n := 354) (q1 := 5) (q2 := 43) (q3 := 47) (q4 := 103) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_360 : 5 ≤ a 360 :=
  five_le_a_of_five_mem (n := 360) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 29) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_366 : 5 ≤ a 366 :=
  five_le_a_of_five_mem (n := 366) (q1 := 7) (q2 := 13) (q3 := 17) (q4 := 53) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_372 : 5 ≤ a 372 :=
  five_le_a_of_five_mem (n := 372) (q1 := 59) (q2 := 61) (q3 := 89) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_378 : 5 ≤ a 378 :=
  five_le_a_of_five_mem (n := 378) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 31) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_384 : 5 ≤ a 384 :=
  five_le_a_of_five_mem (n := 384) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_390 : 5 ≤ a 390 :=
  five_le_a_of_five_mem (n := 390) (q1 := 7) (q2 := 11) (q3 := 31) (q4 := 41) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_396 : 5 ≤ a 396 :=
  five_le_a_of_five_mem (n := 396) (q1 := 13) (q2 := 23) (q3 := 37) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_402 : 5 ≤ a 402 :=
  five_le_a_of_five_mem (n := 402) (q1 := 19) (q2 := 29) (q3 := 89) (q4 := 139) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_408 : 5 ≤ a 408 :=
  five_le_a_of_five_mem (n := 408) (q1 := 11) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_414 : 5 ≤ a 414 :=
  five_le_a_of_five_mem (n := 414) (q1 := 5) (q2 := 17) (q3 := 47) (q4 := 107) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_420 : 5 ≤ a 420 :=
  five_le_a_of_five_mem (n := 420) (q1 := 11) (q2 := 19) (q3 := 23) (q4 := 37) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_426 : 5 ≤ a 426 :=
  five_le_a_of_five_mem (n := 426) (q1 := 5) (q2 := 7) (q3 := 17) (q4 := 37) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_432 : 5 ≤ a 432 :=
  five_le_a_of_five_mem (n := 432) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_438 : 5 ≤ a 438 :=
  five_le_a_of_five_mem (n := 438) (q1 := 5) (q2 := 19) (q3 := 29) (q4 := 41) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_444 : 5 ≤ a 444 :=
  five_le_a_of_five_mem (n := 444) (q1 := 5) (q2 := 13) (q3 := 23) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_450 : 5 ≤ a 450 :=
  five_le_a_of_five_mem (n := 450) (q1 := 7) (q2 := 11) (q3 := 17) (q4 := 29) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_456 : 5 ≤ a 456 :=
  five_le_a_of_five_mem (n := 456) (q1 := 7) (q2 := 23) (q3 := 47) (q4 := 67) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_462 : 5 ≤ a 462 :=
  five_le_a_of_five_mem (n := 462) (q1 := 5) (q2 := 29) (q3 := 41) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_468 : 5 ≤ a 468 :=
  five_le_a_of_five_mem (n := 468) (q1 := 11) (q2 := 19) (q3 := 79) (q4 := 89) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_474 : 5 ≤ a 474 :=
  five_le_a_of_five_mem (n := 474) (q1 := 13) (q2 := 17) (q3 := 73) (q4 := 127) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_480 : 5 ≤ a 480 :=
  five_le_a_of_five_mem (n := 480) (q1 := 19) (q2 := 23) (q3 := 41) (q4 := 61) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_486 : 5 ≤ a 486 :=
  five_le_a_of_five_mem (n := 486) (q1 := 23) (q2 := 37) (q3 := 107) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_492 : 5 ≤ a 492 :=
  five_le_a_of_five_mem (n := 492) (q1 := 29) (q2 := 31) (q3 := 71) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_498 : 5 ≤ a 498 :=
  five_le_a_of_five_mem (n := 498) (q1 := 11) (q2 := 59) (q3 := 79) (q4 := 89) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_504 : 5 ≤ a 504 :=
  five_le_a_of_five_mem (n := 504) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 43) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_510 : 5 ≤ a 510 :=
  five_le_a_of_five_mem (n := 510) (q1 := 11) (q2 := 31) (q3 := 47) (q4 := 53) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_516 : 5 ≤ a 516 :=
  five_le_a_of_five_mem (n := 516) (q1 := 7) (q2 := 53) (q3 := 83) (q4 := 97) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_522 : 5 ≤ a 522 :=
  five_le_a_of_five_mem (n := 522) (q1 := 19) (q2 := 79) (q3 := 139) (q4 := 211) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_528 : 5 ≤ a 528 :=
  five_le_a_of_five_mem (n := 528) (q1 := 19) (q2 := 29) (q3 := 41) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_534 : 5 ≤ a 534 :=
  five_le_a_of_five_mem (n := 534) (q1 := 13) (q2 := 43) (q3 := 67) (q4 := 73) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_540 : 5 ≤ a 540 :=
  five_le_a_of_five_mem (n := 540) (q1 := 17) (q2 := 31) (q3 := 37) (q4 := 53) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_546 : 5 ≤ a 546 :=
  five_le_a_of_five_mem (n := 546) (q1 := 23) (q2 := 47) (q3 := 67) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_552 : 5 ≤ a 552 :=
  five_le_a_of_five_mem (n := 552) (q1 := 5) (q2 := 11) (q3 := 61) (q4 := 89) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_558 : 5 ≤ a 558 :=
  five_le_a_of_five_mem (n := 558) (q1 := 11) (q2 := 59) (q3 := 101) (q4 := 199) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_564 : 5 ≤ a 564 :=
  five_le_a_of_five_mem (n := 564) (q1 := 7) (q2 := 23) (q3 := 43) (q4 := 97) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_570 : 5 ≤ a 570 :=
  five_le_a_of_five_mem (n := 570) (q1 := 7) (q2 := 23) (q3 := 29) (q4 := 47) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_576 : 5 ≤ a 576 :=
  five_le_a_of_five_mem (n := 576) (q1 := 67) (q2 := 97) (q3 := 157) (q4 := 167) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_582 : 5 ≤ a 582 :=
  five_le_a_of_five_mem (n := 582) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 59) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_588 : 5 ≤ a 588 :=
  five_le_a_of_five_mem (n := 588) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_594 : 5 ≤ a 594 :=
  five_le_a_of_five_mem (n := 594) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 47) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_600 : 5 ≤ a 600 :=
  five_le_a_of_five_mem (n := 600) (q1 := 7) (q2 := 13) (q3 := 31) (q4 := 43) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_606 : 5 ≤ a 606 :=
  five_le_a_of_five_mem (n := 606) (q1 := 7) (q2 := 13) (q3 := 37) (q4 := 103) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_612 : 5 ≤ a 612 :=
  five_le_a_of_five_mem (n := 612) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 71) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_618 : 5 ≤ a 618 :=
  five_le_a_of_five_mem (n := 618) (q1 := 41) (q2 := 109) (q3 := 139) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_624 : 5 ≤ a 624 :=
  five_le_a_of_five_mem (n := 624) (q1 := 7) (q2 := 17) (q3 := 23) (q4 := 37) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_630 : 5 ≤ a 630 :=
  five_le_a_of_five_mem (n := 630) (q1 := 11) (q2 := 13) (q3 := 17) (q4 := 23) (q5 := 29)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_636 : 5 ≤ a 636 :=
  five_le_a_of_five_mem (n := 636) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 37) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_642 : 5 ≤ a 642 :=
  five_le_a_of_five_mem (n := 642) (q1 := 11) (q2 := 41) (q3 := 101) (q4 := 179) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_648 : 5 ≤ a 648 :=
  five_le_a_of_five_mem (n := 648) (q1 := 5) (q2 := 29) (q3 := 61) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_654 : 5 ≤ a 654 :=
  five_le_a_of_five_mem (n := 654) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 47) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_660 : 5 ≤ a 660 :=
  five_le_a_of_five_mem (n := 660) (q1 := 13) (q2 := 17) (q3 := 41) (q4 := 59) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_666 : 5 ≤ a 666 :=
  five_le_a_of_five_mem (n := 666) (q1 := 7) (q2 := 53) (q3 := 67) (q4 := 73) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_672 : 5 ≤ a 672 :=
  five_le_a_of_five_mem (n := 672) (q1 := 11) (q2 := 19) (q3 := 29) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_678 : 5 ≤ a 678 :=
  five_le_a_of_five_mem (n := 678) (q1 := 5) (q2 := 31) (q3 := 61) (q4 := 79) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_684 : 5 ≤ a 684 :=
  five_le_a_of_five_mem (n := 684) (q1 := 7) (q2 := 43) (q3 := 67) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_690 : 5 ≤ a 690 :=
  five_le_a_of_five_mem (n := 690) (q1 := 29) (q2 := 37) (q3 := 43) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_696 : 5 ≤ a 696 :=
  five_le_a_of_five_mem (n := 696) (q1 := 5) (q2 := 13) (q3 := 23) (q4 := 37) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_702 : 5 ≤ a 702 :=
  five_le_a_of_five_mem (n := 702) (q1 := 41) (q2 := 59) (q3 := 71) (q4 := 109) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_708 : 5 ≤ a 708 :=
  five_le_a_of_five_mem (n := 708) (q1 := 31) (q2 := 61) (q3 := 89) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_714 : 5 ≤ a 714 :=
  five_le_a_of_five_mem (n := 714) (q1 := 5) (q2 := 13) (q3 := 37) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_720 : 5 ≤ a 720 :=
  five_le_a_of_five_mem (n := 720) (q1 := 19) (q2 := 37) (q3 := 67) (q4 := 89) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_726 : 5 ≤ a 726 :=
  five_le_a_of_five_mem (n := 726) (q1 := 7) (q2 := 17) (q3 := 43) (q4 := 83) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_732 : 5 ≤ a 732 :=
  five_le_a_of_five_mem (n := 732) (q1 := 41) (q2 := 79) (q3 := 89) (q4 := 131) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_738 : 5 ≤ a 738 :=
  five_le_a_of_five_mem (n := 738) (q1 := 5) (q2 := 19) (q3 := 139) (q4 := 181) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_744 : 5 ≤ a 744 :=
  five_le_a_of_five_mem (n := 744) (q1 := 17) (q2 := 43) (q3 := 53) (q4 := 67) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_750 : 5 ≤ a 750 :=
  five_le_a_of_five_mem (n := 750) (q1 := 7) (q2 := 11) (q3 := 23) (q4 := 59) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_756 : 5 ≤ a 756 :=
  five_le_a_of_five_mem (n := 756) (q1 := 5) (q2 := 13) (q3 := 17) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_762 : 5 ≤ a 762 :=
  five_le_a_of_five_mem (n := 762) (q1 := 11) (q2 := 61) (q3 := 101) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_768 : 5 ≤ a 768 :=
  five_le_a_of_five_mem (n := 768) (q1 := 29) (q2 := 41) (q3 := 59) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_774 : 5 ≤ a 774 :=
  five_le_a_of_five_mem (n := 774) (q1 := 13) (q2 := 23) (q3 := 47) (q4 := 83) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_780 : 5 ≤ a 780 :=
  five_le_a_of_five_mem (n := 780) (q1 := 7) (q2 := 29) (q3 := 41) (q4 := 47) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_786 : 5 ≤ a 786 :=
  five_le_a_of_five_mem (n := 786) (q1 := 43) (q2 := 53) (q3 := 67) (q4 := 167) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_792 : 5 ≤ a 792 :=
  five_le_a_of_five_mem (n := 792) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 149) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_798 : 5 ≤ a 798 :=
  five_le_a_of_five_mem (n := 798) (q1 := 11) (q2 := 29) (q3 := 41) (q4 := 59) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_804 : 5 ≤ a 804 :=
  five_le_a_of_five_mem (n := 804) (q1 := 7) (q2 := 17) (q3 := 53) (q4 := 103) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_810 : 5 ≤ a 810 :=
  five_le_a_of_five_mem (n := 810) (q1 := 13) (q2 := 53) (q3 := 67) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_816 : 5 ≤ a 816 :=
  five_le_a_of_five_mem (n := 816) (q1 := 5) (q2 := 7) (q3 := 43) (q4 := 47) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_822 : 5 ≤ a 822 :=
  five_le_a_of_five_mem (n := 822) (q1 := 61) (q2 := 89) (q3 := 131) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_828 : 5 ≤ a 828 :=
  five_le_a_of_five_mem (n := 828) (q1 := 31) (q2 := 59) (q3 := 101) (q4 := 109) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_834 : 5 ≤ a 834 :=
  five_le_a_of_five_mem (n := 834) (q1 := 5) (q2 := 23) (q3 := 47) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_840 : 5 ≤ a 840 :=
  five_le_a_of_five_mem (n := 840) (q1 := 13) (q2 := 17) (q3 := 19) (q4 := 43) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_846 : 5 ≤ a 846 :=
  five_le_a_of_five_mem (n := 846) (q1 := 7) (q2 := 17) (q3 := 37) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_852 : 5 ≤ a 852 :=
  five_le_a_of_five_mem (n := 852) (q1 := 29) (q2 := 31) (q3 := 101) (q4 := 179) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_858 : 5 ≤ a 858 :=
  five_le_a_of_five_mem (n := 858) (q1 := 5) (q2 := 19) (q3 := 29) (q4 := 61) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_864 : 5 ≤ a 864 :=
  five_le_a_of_five_mem (n := 864) (q1 := 43) (q2 := 103) (q3 := 107) (q4 := 113) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_870 : 5 ≤ a 870 :=
  five_le_a_of_five_mem (n := 870) (q1 := 7) (q2 := 11) (q3 := 13) (q4 := 17) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_876 : 5 ≤ a 876 :=
  five_le_a_of_five_mem (n := 876) (q1 := 53) (q2 := 107) (q3 := 137) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_882 : 5 ≤ a 882 :=
  five_le_a_of_five_mem (n := 882) (q1 := 5) (q2 := 29) (q3 := 59) (q4 := 71) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_888 : 5 ≤ a 888 :=
  five_le_a_of_five_mem (n := 888) (q1 := 31) (q2 := 59) (q3 := 79) (q4 := 131) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_894 : 5 ≤ a 894 :=
  five_le_a_of_five_mem (n := 894) (q1 := 13) (q2 := 17) (q3 := 73) (q4 := 83) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_900 : 5 ≤ a 900 :=
  five_le_a_of_five_mem (n := 900) (q1 := 19) (q2 := 37) (q3 := 41) (q4 := 47) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_906 : 5 ≤ a 906 :=
  five_le_a_of_five_mem (n := 906) (q1 := 23) (q2 := 47) (q3 := 163) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_912 : 5 ≤ a 912 :=
  five_le_a_of_five_mem (n := 912) (q1 := 29) (q2 := 59) (q3 := 101) (q4 := 139) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_918 : 5 ≤ a 918 :=
  five_le_a_of_five_mem (n := 918) (q1 := 11) (q2 := 59) (q3 := 79) (q4 := 131) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_924 : 5 ≤ a 924 :=
  five_le_a_of_five_mem (n := 924) (q1 := 5) (q2 := 13) (q3 := 17) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_930 : 5 ≤ a 930 :=
  five_le_a_of_five_mem (n := 930) (q1 := 11) (q2 := 23) (q3 := 47) (q4 := 53) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_936 : 5 ≤ a 936 :=
  five_le_a_of_five_mem (n := 936) (q1 := 17) (q2 := 73) (q3 := 83) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_942 : 5 ≤ a 942 :=
  five_le_a_of_five_mem (n := 942) (q1 := 5) (q2 := 79) (q3 := 89) (q4 := 181) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_948 : 5 ≤ a 948 :=
  five_le_a_of_five_mem (n := 948) (q1 := 19) (q2 := 29) (q3 := 61) (q4 := 71) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_954 : 5 ≤ a 954 :=
  five_le_a_of_five_mem (n := 954) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 67) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_960 : 5 ≤ a 960 :=
  five_le_a_of_five_mem (n := 960) (q1 := 7) (q2 := 23) (q3 := 31) (q4 := 53) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_966 : 5 ≤ a 966 :=
  five_le_a_of_five_mem (n := 966) (q1 := 47) (q2 := 83) (q3 := 103) (q4 := 127) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_972 : 5 ≤ a 972 :=
  five_le_a_of_five_mem (n := 972) (q1 := 5) (q2 := 19) (q3 := 61) (q4 := 89) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_978 : 5 ≤ a 978 :=
  five_le_a_of_five_mem (n := 978) (q1 := 31) (q2 := 41) (q3 := 71) (q4 := 139) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_984 : 5 ≤ a 984 :=
  five_le_a_of_five_mem (n := 984) (q1 := 7) (q2 := 13) (q3 := 37) (q4 := 47) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_990 : 5 ≤ a 990 :=
  five_le_a_of_five_mem (n := 990) (q1 := 7) (q2 := 19) (q3 := 23) (q4 := 43) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_996 : 5 ≤ a 996 :=
  five_le_a_of_five_mem (n := 996) (q1 := 13) (q2 := 43) (q3 := 67) (q4 := 113) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1002 : 5 ≤ a 1002 :=
  five_le_a_of_five_mem (n := 1002) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 61) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1008 : 5 ≤ a 1008 :=
  five_le_a_of_five_mem (n := 1008) (q1 := 11) (q2 := 31) (q3 := 41) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1014 : 5 ≤ a 1014 :=
  five_le_a_of_five_mem (n := 1014) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1020 : 5 ≤ a 1020 :=
  five_le_a_of_five_mem (n := 1020) (q1 := 11) (q2 := 29) (q3 := 43) (q4 := 67) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1026 : 5 ≤ a 1026 :=
  five_le_a_of_five_mem (n := 1026) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 43) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1032 : 5 ≤ a 1032 :=
  five_le_a_of_five_mem (n := 1032) (q1 := 19) (q2 := 61) (q3 := 149) (q4 := 271) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1038 : 5 ≤ a 1038 :=
  five_le_a_of_five_mem (n := 1038) (q1 := 71) (q2 := 179) (q3 := 199) (q4 := 211) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1044 : 5 ≤ a 1044 :=
  five_le_a_of_five_mem (n := 1044) (q1 := 5) (q2 := 47) (q3 := 53) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1050 : 5 ≤ a 1050 :=
  five_le_a_of_five_mem (n := 1050) (q1 := 11) (q2 := 19) (q3 := 37) (q4 := 41) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1056 : 5 ≤ a 1056 :=
  five_le_a_of_five_mem (n := 1056) (q1 := 5) (q2 := 7) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1062 : 5 ≤ a 1062 :=
  five_le_a_of_five_mem (n := 1062) (q1 := 29) (q2 := 31) (q3 := 41) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1068 : 5 ≤ a 1068 :=
  five_le_a_of_five_mem (n := 1068) (q1 := 19) (q2 := 29) (q3 := 149) (q4 := 181) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1074 : 5 ≤ a 1074 :=
  five_le_a_of_five_mem (n := 1074) (q1 := 13) (q2 := 23) (q3 := 43) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1080 : 5 ≤ a 1080 :=
  five_le_a_of_five_mem (n := 1080) (q1 := 11) (q2 := 17) (q3 := 29) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1086 : 5 ≤ a 1086 :=
  five_le_a_of_five_mem (n := 1086) (q1 := 17) (q2 := 23) (q3 := 37) (q4 := 67) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1092 : 5 ≤ a 1092 :=
  five_le_a_of_five_mem (n := 1092) (q1 := 5) (q2 := 31) (q3 := 59) (q4 := 61) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1098 : 5 ≤ a 1098 :=
  five_le_a_of_five_mem (n := 1098) (q1 := 5) (q2 := 11) (q3 := 89) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1104 : 5 ≤ a 1104 :=
  five_le_a_of_five_mem (n := 1104) (q1 := 13) (q2 := 83) (q3 := 113) (q4 := 127) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1110 : 5 ≤ a 1110 :=
  five_le_a_of_five_mem (n := 1110) (q1 := 7) (q2 := 13) (q3 := 19) (q4 := 41) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1116 : 5 ≤ a 1116 :=
  five_le_a_of_five_mem (n := 1116) (q1 := 7) (q2 := 13) (q3 := 47) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1122 : 5 ≤ a 1122 :=
  five_le_a_of_five_mem (n := 1122) (q1 := 29) (q2 := 31) (q3 := 59) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1128 : 5 ≤ a 1128 :=
  five_le_a_of_five_mem (n := 1128) (q1 := 59) (q2 := 89) (q3 := 109) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1134 : 5 ≤ a 1134 :=
  five_le_a_of_five_mem (n := 1134) (q1 := 17) (q2 := 37) (q3 := 47) (q4 := 83) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1140 : 5 ≤ a 1140 :=
  five_le_a_of_five_mem (n := 1140) (q1 := 11) (q2 := 23) (q3 := 31) (q4 := 47) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1146 : 5 ≤ a 1146 :=
  five_le_a_of_five_mem (n := 1146) (q1 := 17) (q2 := 83) (q3 := 113) (q4 := 137) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1152 : 5 ≤ a 1152 :=
  five_le_a_of_five_mem (n := 1152) (q1 := 29) (q2 := 61) (q3 := 131) (q4 := 139) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1158 : 5 ≤ a 1158 :=
  five_le_a_of_five_mem (n := 1158) (q1 := 5) (q2 := 29) (q3 := 71) (q4 := 139) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1164 : 5 ≤ a 1164 :=
  five_le_a_of_five_mem (n := 1164) (q1 := 67) (q2 := 73) (q3 := 113) (q4 := 197) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1170 : 5 ≤ a 1170 :=
  five_le_a_of_five_mem (n := 1170) (q1 := 17) (q2 := 47) (q3 := 53) (q4 := 61) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1176 : 5 ≤ a 1176 :=
  five_le_a_of_five_mem (n := 1176) (q1 := 5) (q2 := 47) (q3 := 53) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1182 : 5 ≤ a 1182 :=
  five_le_a_of_five_mem (n := 1182) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1188 : 5 ≤ a 1188 :=
  five_le_a_of_five_mem (n := 1188) (q1 := 71) (q2 := 101) (q3 := 139) (q4 := 179) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1194 : 5 ≤ a 1194 :=
  five_le_a_of_five_mem (n := 1194) (q1 := 7) (q2 := 23) (q3 := 43) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1200 : 5 ≤ a 1200 :=
  five_le_a_of_five_mem (n := 1200) (q1 := 13) (q2 := 29) (q3 := 37) (q4 := 83) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_chunk_0 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 24 ≤ n) (hle : n ≤ 138) : 5 ≤ a n := by
  if h : n = 24 then
    subst h; exact five_le_a_24
  else if h : n = 30 then
    subst h; exact five_le_a_30
  else if h : n = 36 then
    subst h; exact five_le_a_36
  else if h : n = 42 then
    subst h; exact five_le_a_42
  else if h : n = 48 then
    subst h; exact five_le_a_48
  else if h : n = 54 then
    subst h; exact five_le_a_54
  else if h : n = 60 then
    subst h; exact five_le_a_60
  else if h : n = 66 then
    subst h; exact five_le_a_66
  else if h : n = 72 then
    subst h; exact five_le_a_72
  else if h : n = 78 then
    subst h; exact five_le_a_78
  else if h : n = 84 then
    subst h; exact five_le_a_84
  else if h : n = 90 then
    subst h; exact five_le_a_90
  else if h : n = 96 then
    subst h; exact five_le_a_96
  else if h : n = 102 then
    subst h; exact five_le_a_102
  else if h : n = 108 then
    subst h; exact five_le_a_108
  else if h : n = 114 then
    subst h; exact five_le_a_114
  else if h : n = 120 then
    subst h; exact five_le_a_120
  else if h : n = 126 then
    subst h; exact five_le_a_126
  else if h : n = 132 then
    subst h; exact five_le_a_132
  else if h : n = 138 then
    subst h; exact five_le_a_138
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_1 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 144 ≤ n) (hle : n ≤ 258) : 5 ≤ a n := by
  if h : n = 144 then
    subst h; exact five_le_a_144
  else if h : n = 150 then
    subst h; exact five_le_a_150
  else if h : n = 156 then
    subst h; exact five_le_a_156
  else if h : n = 162 then
    subst h; exact five_le_a_162
  else if h : n = 168 then
    subst h; exact five_le_a_168
  else if h : n = 174 then
    subst h; exact five_le_a_174
  else if h : n = 180 then
    subst h; exact five_le_a_180
  else if h : n = 186 then
    subst h; exact five_le_a_186
  else if h : n = 192 then
    subst h; exact five_le_a_192
  else if h : n = 198 then
    subst h; exact five_le_a_198
  else if h : n = 204 then
    subst h; exact five_le_a_204
  else if h : n = 210 then
    subst h; exact five_le_a_210
  else if h : n = 216 then
    subst h; exact five_le_a_216
  else if h : n = 222 then
    subst h; exact five_le_a_222
  else if h : n = 228 then
    subst h; exact five_le_a_228
  else if h : n = 234 then
    subst h; exact five_le_a_234
  else if h : n = 240 then
    subst h; exact five_le_a_240
  else if h : n = 246 then
    subst h; exact five_le_a_246
  else if h : n = 252 then
    subst h; exact five_le_a_252
  else if h : n = 258 then
    subst h; exact five_le_a_258
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_2 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 264 ≤ n) (hle : n ≤ 378) : 5 ≤ a n := by
  if h : n = 264 then
    subst h; exact five_le_a_264
  else if h : n = 270 then
    subst h; exact five_le_a_270
  else if h : n = 276 then
    subst h; exact five_le_a_276
  else if h : n = 282 then
    subst h; exact five_le_a_282
  else if h : n = 288 then
    subst h; exact five_le_a_288
  else if h : n = 294 then
    subst h; exact five_le_a_294
  else if h : n = 300 then
    subst h; exact five_le_a_300
  else if h : n = 306 then
    subst h; exact five_le_a_306
  else if h : n = 312 then
    subst h; exact five_le_a_312
  else if h : n = 318 then
    subst h; exact five_le_a_318
  else if h : n = 324 then
    subst h; exact five_le_a_324
  else if h : n = 330 then
    subst h; exact five_le_a_330
  else if h : n = 336 then
    subst h; exact five_le_a_336
  else if h : n = 342 then
    subst h; exact five_le_a_342
  else if h : n = 348 then
    subst h; exact five_le_a_348
  else if h : n = 354 then
    subst h; exact five_le_a_354
  else if h : n = 360 then
    subst h; exact five_le_a_360
  else if h : n = 366 then
    subst h; exact five_le_a_366
  else if h : n = 372 then
    subst h; exact five_le_a_372
  else if h : n = 378 then
    subst h; exact five_le_a_378
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_3 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 384 ≤ n) (hle : n ≤ 498) : 5 ≤ a n := by
  if h : n = 384 then
    subst h; exact five_le_a_384
  else if h : n = 390 then
    subst h; exact five_le_a_390
  else if h : n = 396 then
    subst h; exact five_le_a_396
  else if h : n = 402 then
    subst h; exact five_le_a_402
  else if h : n = 408 then
    subst h; exact five_le_a_408
  else if h : n = 414 then
    subst h; exact five_le_a_414
  else if h : n = 420 then
    subst h; exact five_le_a_420
  else if h : n = 426 then
    subst h; exact five_le_a_426
  else if h : n = 432 then
    subst h; exact five_le_a_432
  else if h : n = 438 then
    subst h; exact five_le_a_438
  else if h : n = 444 then
    subst h; exact five_le_a_444
  else if h : n = 450 then
    subst h; exact five_le_a_450
  else if h : n = 456 then
    subst h; exact five_le_a_456
  else if h : n = 462 then
    subst h; exact five_le_a_462
  else if h : n = 468 then
    subst h; exact five_le_a_468
  else if h : n = 474 then
    subst h; exact five_le_a_474
  else if h : n = 480 then
    subst h; exact five_le_a_480
  else if h : n = 486 then
    subst h; exact five_le_a_486
  else if h : n = 492 then
    subst h; exact five_le_a_492
  else if h : n = 498 then
    subst h; exact five_le_a_498
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_4 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 504 ≤ n) (hle : n ≤ 618) : 5 ≤ a n := by
  if h : n = 504 then
    subst h; exact five_le_a_504
  else if h : n = 510 then
    subst h; exact five_le_a_510
  else if h : n = 516 then
    subst h; exact five_le_a_516
  else if h : n = 522 then
    subst h; exact five_le_a_522
  else if h : n = 528 then
    subst h; exact five_le_a_528
  else if h : n = 534 then
    subst h; exact five_le_a_534
  else if h : n = 540 then
    subst h; exact five_le_a_540
  else if h : n = 546 then
    subst h; exact five_le_a_546
  else if h : n = 552 then
    subst h; exact five_le_a_552
  else if h : n = 558 then
    subst h; exact five_le_a_558
  else if h : n = 564 then
    subst h; exact five_le_a_564
  else if h : n = 570 then
    subst h; exact five_le_a_570
  else if h : n = 576 then
    subst h; exact five_le_a_576
  else if h : n = 582 then
    subst h; exact five_le_a_582
  else if h : n = 588 then
    subst h; exact five_le_a_588
  else if h : n = 594 then
    subst h; exact five_le_a_594
  else if h : n = 600 then
    subst h; exact five_le_a_600
  else if h : n = 606 then
    subst h; exact five_le_a_606
  else if h : n = 612 then
    subst h; exact five_le_a_612
  else if h : n = 618 then
    subst h; exact five_le_a_618
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_5 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 624 ≤ n) (hle : n ≤ 738) : 5 ≤ a n := by
  if h : n = 624 then
    subst h; exact five_le_a_624
  else if h : n = 630 then
    subst h; exact five_le_a_630
  else if h : n = 636 then
    subst h; exact five_le_a_636
  else if h : n = 642 then
    subst h; exact five_le_a_642
  else if h : n = 648 then
    subst h; exact five_le_a_648
  else if h : n = 654 then
    subst h; exact five_le_a_654
  else if h : n = 660 then
    subst h; exact five_le_a_660
  else if h : n = 666 then
    subst h; exact five_le_a_666
  else if h : n = 672 then
    subst h; exact five_le_a_672
  else if h : n = 678 then
    subst h; exact five_le_a_678
  else if h : n = 684 then
    subst h; exact five_le_a_684
  else if h : n = 690 then
    subst h; exact five_le_a_690
  else if h : n = 696 then
    subst h; exact five_le_a_696
  else if h : n = 702 then
    subst h; exact five_le_a_702
  else if h : n = 708 then
    subst h; exact five_le_a_708
  else if h : n = 714 then
    subst h; exact five_le_a_714
  else if h : n = 720 then
    subst h; exact five_le_a_720
  else if h : n = 726 then
    subst h; exact five_le_a_726
  else if h : n = 732 then
    subst h; exact five_le_a_732
  else if h : n = 738 then
    subst h; exact five_le_a_738
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_6 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 744 ≤ n) (hle : n ≤ 858) : 5 ≤ a n := by
  if h : n = 744 then
    subst h; exact five_le_a_744
  else if h : n = 750 then
    subst h; exact five_le_a_750
  else if h : n = 756 then
    subst h; exact five_le_a_756
  else if h : n = 762 then
    subst h; exact five_le_a_762
  else if h : n = 768 then
    subst h; exact five_le_a_768
  else if h : n = 774 then
    subst h; exact five_le_a_774
  else if h : n = 780 then
    subst h; exact five_le_a_780
  else if h : n = 786 then
    subst h; exact five_le_a_786
  else if h : n = 792 then
    subst h; exact five_le_a_792
  else if h : n = 798 then
    subst h; exact five_le_a_798
  else if h : n = 804 then
    subst h; exact five_le_a_804
  else if h : n = 810 then
    subst h; exact five_le_a_810
  else if h : n = 816 then
    subst h; exact five_le_a_816
  else if h : n = 822 then
    subst h; exact five_le_a_822
  else if h : n = 828 then
    subst h; exact five_le_a_828
  else if h : n = 834 then
    subst h; exact five_le_a_834
  else if h : n = 840 then
    subst h; exact five_le_a_840
  else if h : n = 846 then
    subst h; exact five_le_a_846
  else if h : n = 852 then
    subst h; exact five_le_a_852
  else if h : n = 858 then
    subst h; exact five_le_a_858
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_7 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 864 ≤ n) (hle : n ≤ 978) : 5 ≤ a n := by
  if h : n = 864 then
    subst h; exact five_le_a_864
  else if h : n = 870 then
    subst h; exact five_le_a_870
  else if h : n = 876 then
    subst h; exact five_le_a_876
  else if h : n = 882 then
    subst h; exact five_le_a_882
  else if h : n = 888 then
    subst h; exact five_le_a_888
  else if h : n = 894 then
    subst h; exact five_le_a_894
  else if h : n = 900 then
    subst h; exact five_le_a_900
  else if h : n = 906 then
    subst h; exact five_le_a_906
  else if h : n = 912 then
    subst h; exact five_le_a_912
  else if h : n = 918 then
    subst h; exact five_le_a_918
  else if h : n = 924 then
    subst h; exact five_le_a_924
  else if h : n = 930 then
    subst h; exact five_le_a_930
  else if h : n = 936 then
    subst h; exact five_le_a_936
  else if h : n = 942 then
    subst h; exact five_le_a_942
  else if h : n = 948 then
    subst h; exact five_le_a_948
  else if h : n = 954 then
    subst h; exact five_le_a_954
  else if h : n = 960 then
    subst h; exact five_le_a_960
  else if h : n = 966 then
    subst h; exact five_le_a_966
  else if h : n = 972 then
    subst h; exact five_le_a_972
  else if h : n = 978 then
    subst h; exact five_le_a_978
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_8 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 984 ≤ n) (hle : n ≤ 1098) : 5 ≤ a n := by
  if h : n = 984 then
    subst h; exact five_le_a_984
  else if h : n = 990 then
    subst h; exact five_le_a_990
  else if h : n = 996 then
    subst h; exact five_le_a_996
  else if h : n = 1002 then
    subst h; exact five_le_a_1002
  else if h : n = 1008 then
    subst h; exact five_le_a_1008
  else if h : n = 1014 then
    subst h; exact five_le_a_1014
  else if h : n = 1020 then
    subst h; exact five_le_a_1020
  else if h : n = 1026 then
    subst h; exact five_le_a_1026
  else if h : n = 1032 then
    subst h; exact five_le_a_1032
  else if h : n = 1038 then
    subst h; exact five_le_a_1038
  else if h : n = 1044 then
    subst h; exact five_le_a_1044
  else if h : n = 1050 then
    subst h; exact five_le_a_1050
  else if h : n = 1056 then
    subst h; exact five_le_a_1056
  else if h : n = 1062 then
    subst h; exact five_le_a_1062
  else if h : n = 1068 then
    subst h; exact five_le_a_1068
  else if h : n = 1074 then
    subst h; exact five_le_a_1074
  else if h : n = 1080 then
    subst h; exact five_le_a_1080
  else if h : n = 1086 then
    subst h; exact five_le_a_1086
  else if h : n = 1092 then
    subst h; exact five_le_a_1092
  else if h : n = 1098 then
    subst h; exact five_le_a_1098
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_9 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1104 ≤ n) (hle : n ≤ 1200) : 5 ≤ a n := by
  if h : n = 1104 then
    subst h; exact five_le_a_1104
  else if h : n = 1110 then
    subst h; exact five_le_a_1110
  else if h : n = 1116 then
    subst h; exact five_le_a_1116
  else if h : n = 1122 then
    subst h; exact five_le_a_1122
  else if h : n = 1128 then
    subst h; exact five_le_a_1128
  else if h : n = 1134 then
    subst h; exact five_le_a_1134
  else if h : n = 1140 then
    subst h; exact five_le_a_1140
  else if h : n = 1146 then
    subst h; exact five_le_a_1146
  else if h : n = 1152 then
    subst h; exact five_le_a_1152
  else if h : n = 1158 then
    subst h; exact five_le_a_1158
  else if h : n = 1164 then
    subst h; exact five_le_a_1164
  else if h : n = 1170 then
    subst h; exact five_le_a_1170
  else if h : n = 1176 then
    subst h; exact five_le_a_1176
  else if h : n = 1182 then
    subst h; exact five_le_a_1182
  else if h : n = 1188 then
    subst h; exact five_le_a_1188
  else if h : n = 1194 then
    subst h; exact five_le_a_1194
  else if h : n = 1200 then
    subst h; exact five_le_a_1200
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_of_dvd_six_ge_24_le_1200 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 24 ≤ n) (hle : n ≤ 1200) : 5 ≤ a n := by
  if h : n ≤ 138 then
    exact five_le_a_chunk_0 h6 (by omega) h
  else if h : n ≤ 258 then
    exact five_le_a_chunk_1 h6 (by omega) h
  else if h : n ≤ 378 then
    exact five_le_a_chunk_2 h6 (by omega) h
  else if h : n ≤ 498 then
    exact five_le_a_chunk_3 h6 (by omega) h
  else if h : n ≤ 618 then
    exact five_le_a_chunk_4 h6 (by omega) h
  else if h : n ≤ 738 then
    exact five_le_a_chunk_5 h6 (by omega) h
  else if h : n ≤ 858 then
    exact five_le_a_chunk_6 h6 (by omega) h
  else if h : n ≤ 978 then
    exact five_le_a_chunk_7 h6 (by omega) h
  else if h : n ≤ 1098 then
    exact five_le_a_chunk_8 h6 (by omega) h
  else if h : n ≤ 1200 then
    exact five_le_a_chunk_9 h6 (by omega) h
  else
    omega

lemma a_ne_four_of_dvd_six_of_lt_24 {n : ℕ} (h6 : 6 ∣ n) (h : n < 24) : a n ≠ 4 := by
  have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
  interval_cases n <;> first | decide | omega

lemma a_ne_four_of_le_1200 {n : ℕ} (hle : n ≤ 1200) : a n ≠ 4 := by
  by_cases h6 : 6 ∣ n
  · by_cases hlt : n < 24
    · exact a_ne_four_of_dvd_six_of_lt_24 h6 hlt
    · have : 5 ≤ a n := five_le_a_of_dvd_six_ge_24_le_1200 h6 (by omega) hle
      omega
  · exact a_ne_four_of_not_dvd_six h6
