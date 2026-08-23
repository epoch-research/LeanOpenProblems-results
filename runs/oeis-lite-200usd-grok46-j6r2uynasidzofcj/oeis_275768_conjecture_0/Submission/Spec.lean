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

lemma five_le_a_1206 : 5 ≤ a 1206 :=
  five_le_a_of_five_mem (n := 1206) (q1 := 43) (q2 := 53) (q3 := 83) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1212 : 5 ≤ a 1212 :=
  five_le_a_of_five_mem (n := 1212) (q1 := 11) (q2 := 19) (q3 := 89) (q4 := 109) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1218 : 5 ≤ a 1218 :=
  five_le_a_of_five_mem (n := 1218) (q1 := 5) (q2 := 31) (q3 := 89) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1224 : 5 ≤ a 1224 :=
  five_le_a_of_five_mem (n := 1224) (q1 := 7) (q2 := 53) (q3 := 73) (q4 := 137) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1230 : 5 ≤ a 1230 :=
  five_le_a_of_five_mem (n := 1230) (q1 := 7) (q2 := 29) (q3 := 59) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1236 : 5 ≤ a 1236 :=
  five_le_a_of_five_mem (n := 1236) (q1 := 13) (q2 := 23) (q3 := 43) (q4 := 83) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1242 : 5 ≤ a 1242 :=
  five_le_a_of_five_mem (n := 1242) (q1 := 41) (q2 := 61) (q3 := 79) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1248 : 5 ≤ a 1248 :=
  five_le_a_of_five_mem (n := 1248) (q1 := 11) (q2 := 31) (q3 := 151) (q4 := 179) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1254 : 5 ≤ a 1254 :=
  five_le_a_of_five_mem (n := 1254) (q1 := 5) (q2 := 23) (q3 := 37) (q4 := 53) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1260 : 5 ≤ a 1260 :=
  five_le_a_of_five_mem (n := 1260) (q1 := 23) (q2 := 29) (q3 := 31) (q4 := 37) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1266 : 5 ≤ a 1266 :=
  five_le_a_of_five_mem (n := 1266) (q1 := 17) (q2 := 37) (q3 := 53) (q4 := 157) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1272 : 5 ≤ a 1272 :=
  five_le_a_of_five_mem (n := 1272) (q1 := 101) (q2 := 109) (q3 := 179) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1278 : 5 ≤ a 1278 :=
  five_le_a_of_five_mem (n := 1278) (q1 := 19) (q2 := 29) (q3 := 41) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1284 : 5 ≤ a 1284 :=
  five_le_a_of_five_mem (n := 1284) (q1 := 5) (q2 := 7) (q3 := 83) (q4 := 97) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1290 : 5 ≤ a 1290 :=
  five_le_a_of_five_mem (n := 1290) (q1 := 7) (q2 := 11) (q3 := 13) (q4 := 31) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1296 : 5 ≤ a 1296 :=
  five_le_a_of_five_mem (n := 1296) (q1 := 5) (q2 := 7) (q3 := 103) (q4 := 193) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1302 : 5 ≤ a 1302 :=
  five_le_a_of_five_mem (n := 1302) (q1 := 5) (q2 := 19) (q3 := 71) (q4 := 79) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1308 : 5 ≤ a 1308 :=
  five_le_a_of_five_mem (n := 1308) (q1 := 11) (q2 := 19) (q3 := 59) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1314 : 5 ≤ a 1314 :=
  five_le_a_of_five_mem (n := 1314) (q1 := 7) (q2 := 13) (q3 := 113) (q4 := 197) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1320 : 5 ≤ a 1320 :=
  five_le_a_of_five_mem (n := 1320) (q1 := 41) (q2 := 61) (q3 := 89) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1326 : 5 ≤ a 1326 :=
  five_le_a_of_five_mem (n := 1326) (q1 := 47) (q2 := 97) (q3 := 103) (q4 := 113) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1332 : 5 ≤ a 1332 :=
  five_le_a_of_five_mem (n := 1332) (q1 := 29) (q2 := 41) (q3 := 101) (q4 := 139) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1338 : 5 ≤ a 1338 :=
  five_le_a_of_five_mem (n := 1338) (q1 := 61) (q2 := 89) (q3 := 101) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1344 : 5 ≤ a 1344 :=
  five_le_a_of_five_mem (n := 1344) (q1 := 17) (q2 := 23) (q3 := 37) (q4 := 107) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1350 : 5 ≤ a 1350 :=
  five_le_a_of_five_mem (n := 1350) (q1 := 23) (q2 := 31) (q3 := 59) (q4 := 73) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1356 : 5 ≤ a 1356 :=
  five_le_a_of_five_mem (n := 1356) (q1 := 53) (q2 := 67) (q3 := 73) (q4 := 97) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1362 : 5 ≤ a 1362 :=
  five_le_a_of_five_mem (n := 1362) (q1 := 61) (q2 := 71) (q3 := 131) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1368 : 5 ≤ a 1368 :=
  five_le_a_of_five_mem (n := 1368) (q1 := 41) (q2 := 61) (q3 := 71) (q4 := 79) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1374 : 5 ≤ a 1374 :=
  five_le_a_of_five_mem (n := 1374) (q1 := 7) (q2 := 53) (q3 := 73) (q4 := 97) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1380 : 5 ≤ a 1380 :=
  five_le_a_of_five_mem (n := 1380) (q1 := 19) (q2 := 53) (q3 := 59) (q4 := 73) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1386 : 5 ≤ a 1386 :=
  five_le_a_of_five_mem (n := 1386) (q1 := 13) (q2 := 67) (q3 := 97) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1392 : 5 ≤ a 1392 :=
  five_le_a_of_five_mem (n := 1392) (q1 := 31) (q2 := 89) (q3 := 101) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1398 : 5 ≤ a 1398 :=
  five_le_a_of_five_mem (n := 1398) (q1 := 31) (q2 := 101) (q3 := 181) (q4 := 211) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1404 : 5 ≤ a 1404 :=
  five_le_a_of_five_mem (n := 1404) (q1 := 5) (q2 := 23) (q3 := 43) (q4 := 83) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1410 : 5 ≤ a 1410 :=
  five_le_a_of_five_mem (n := 1410) (q1 := 29) (q2 := 37) (q3 := 43) (q4 := 83) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1416 : 5 ≤ a 1416 :=
  five_le_a_of_five_mem (n := 1416) (q1 := 7) (q2 := 17) (q3 := 43) (q4 := 127) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1422 : 5 ≤ a 1422 :=
  five_le_a_of_five_mem (n := 1422) (q1 := 61) (q2 := 101) (q3 := 131) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1428 : 5 ≤ a 1428 :=
  five_le_a_of_five_mem (n := 1428) (q1 := 5) (q2 := 19) (q3 := 61) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1434 : 5 ≤ a 1434 :=
  five_le_a_of_five_mem (n := 1434) (q1 := 5) (q2 := 53) (q3 := 137) (q4 := 233) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1440 : 5 ≤ a 1440 :=
  five_le_a_of_five_mem (n := 1440) (q1 := 7) (q2 := 11) (q3 := 13) (q4 := 31) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1446 : 5 ≤ a 1446 :=
  five_le_a_of_five_mem (n := 1446) (q1 := 7) (q2 := 13) (q3 := 37) (q4 := 47) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1452 : 5 ≤ a 1452 :=
  five_le_a_of_five_mem (n := 1452) (q1 := 19) (q2 := 29) (q3 := 71) (q4 := 79) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1458 : 5 ≤ a 1458 :=
  five_le_a_of_five_mem (n := 1458) (q1 := 29) (q2 := 31) (q3 := 139) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1464 : 5 ≤ a 1464 :=
  five_le_a_of_five_mem (n := 1464) (q1 := 17) (q2 := 103) (q3 := 137) (q4 := 157) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1470 : 5 ≤ a 1470 :=
  five_le_a_of_five_mem (n := 1470) (q1 := 11) (q2 := 17) (q3 := 19) (q4 := 23) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1476 : 5 ≤ a 1476 :=
  five_le_a_of_five_mem (n := 1476) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1482 : 5 ≤ a 1482 :=
  five_le_a_of_five_mem (n := 1482) (q1 := 11) (q2 := 29) (q3 := 101) (q4 := 181) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1488 : 5 ≤ a 1488 :=
  five_le_a_of_five_mem (n := 1488) (q1 := 5) (q2 := 61) (q3 := 79) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1494 : 5 ≤ a 1494 :=
  five_le_a_of_five_mem (n := 1494) (q1 := 5) (q2 := 113) (q3 := 127) (q4 := 173) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1500 : 5 ≤ a 1500 :=
  five_le_a_of_five_mem (n := 1500) (q1 := 11) (q2 := 53) (q3 := 67) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1506 : 5 ≤ a 1506 :=
  five_le_a_of_five_mem (n := 1506) (q1 := 17) (q2 := 47) (q3 := 53) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1512 : 5 ≤ a 1512 :=
  five_le_a_of_five_mem (n := 1512) (q1 := 19) (q2 := 31) (q3 := 41) (q4 := 59) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1518 : 5 ≤ a 1518 :=
  five_le_a_of_five_mem (n := 1518) (q1 := 31) (q2 := 79) (q3 := 89) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1524 : 5 ≤ a 1524 :=
  five_le_a_of_five_mem (n := 1524) (q1 := 43) (q2 := 73) (q3 := 97) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1530 : 5 ≤ a 1530 :=
  five_le_a_of_five_mem (n := 1530) (q1 := 19) (q2 := 37) (q3 := 41) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1536 : 5 ≤ a 1536 :=
  five_le_a_of_five_mem (n := 1536) (q1 := 13) (q2 := 43) (q3 := 47) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1542 : 5 ≤ a 1542 :=
  five_le_a_of_five_mem (n := 1542) (q1 := 11) (q2 := 59) (q3 := 71) (q4 := 181) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1548 : 5 ≤ a 1548 :=
  five_le_a_of_five_mem (n := 1548) (q1 := 5) (q2 := 59) (q3 := 61) (q4 := 89) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1554 : 5 ≤ a 1554 :=
  five_le_a_of_five_mem (n := 1554) (q1 := 5) (q2 := 43) (q3 := 67) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1560 : 5 ≤ a 1560 :=
  five_le_a_of_five_mem (n := 1560) (q1 := 7) (q2 := 11) (q3 := 37) (q4 := 61) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1566 : 5 ≤ a 1566 :=
  five_le_a_of_five_mem (n := 1566) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 127) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1572 : 5 ≤ a 1572 :=
  five_le_a_of_five_mem (n := 1572) (q1 := 29) (q2 := 41) (q3 := 149) (q4 := 211) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1578 : 5 ≤ a 1578 :=
  five_le_a_of_five_mem (n := 1578) (q1 := 19) (q2 := 29) (q3 := 79) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1584 : 5 ≤ a 1584 :=
  five_le_a_of_five_mem (n := 1584) (q1 := 13) (q2 := 17) (q3 := 53) (q4 := 73) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1590 : 5 ≤ a 1590 :=
  five_le_a_of_five_mem (n := 1590) (q1 := 7) (q2 := 11) (q3 := 19) (q4 := 23) (q5 := 31)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1596 : 5 ≤ a 1596 :=
  five_le_a_of_five_mem (n := 1596) (q1 := 13) (q2 := 17) (q3 := 73) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1602 : 5 ≤ a 1602 :=
  five_le_a_of_five_mem (n := 1602) (q1 := 5) (q2 := 19) (q3 := 131) (q4 := 151) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1608 : 5 ≤ a 1608 :=
  five_le_a_of_five_mem (n := 1608) (q1 := 11) (q2 := 29) (q3 := 59) (q4 := 179) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1614 : 5 ≤ a 1614 :=
  five_le_a_of_five_mem (n := 1614) (q1 := 5) (q2 := 7) (q3 := 13) (q4 := 43) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1620 : 5 ≤ a 1620 :=
  five_le_a_of_five_mem (n := 1620) (q1 := 7) (q2 := 37) (q3 := 89) (q4 := 127) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1626 : 5 ≤ a 1626 :=
  five_le_a_of_five_mem (n := 1626) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1632 : 5 ≤ a 1632 :=
  five_le_a_of_five_mem (n := 1632) (q1 := 5) (q2 := 31) (q3 := 61) (q4 := 89) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1638 : 5 ≤ a 1638 :=
  five_le_a_of_five_mem (n := 1638) (q1 := 19) (q2 := 29) (q3 := 31) (q4 := 59) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1644 : 5 ≤ a 1644 :=
  five_le_a_of_five_mem (n := 1644) (q1 := 23) (q2 := 157) (q3 := 263) (q4 := 353) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1650 : 5 ≤ a 1650 :=
  five_le_a_of_five_mem (n := 1650) (q1 := 13) (q2 := 43) (q3 := 71) (q4 := 83) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1656 : 5 ≤ a 1656 :=
  five_le_a_of_five_mem (n := 1656) (q1 := 37) (q2 := 43) (q3 := 97) (q4 := 103) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1662 : 5 ≤ a 1662 :=
  five_le_a_of_five_mem (n := 1662) (q1 := 5) (q2 := 61) (q3 := 79) (q4 := 139) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1668 : 5 ≤ a 1668 :=
  five_le_a_of_five_mem (n := 1668) (q1 := 31) (q2 := 41) (q3 := 109) (q4 := 179) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1674 : 5 ≤ a 1674 :=
  five_le_a_of_five_mem (n := 1674) (q1 := 47) (q2 := 67) (q3 := 73) (q4 := 103) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1680 : 5 ≤ a 1680 :=
  five_le_a_of_five_mem (n := 1680) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 53) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1686 : 5 ≤ a 1686 :=
  five_le_a_of_five_mem (n := 1686) (q1 := 23) (q2 := 67) (q3 := 73) (q4 := 103) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1692 : 5 ≤ a 1692 :=
  five_le_a_of_five_mem (n := 1692) (q1 := 29) (q2 := 109) (q3 := 139) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1698 : 5 ≤ a 1698 :=
  five_le_a_of_five_mem (n := 1698) (q1 := 61) (q2 := 79) (q3 := 89) (q4 := 149) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1704 : 5 ≤ a 1704 :=
  five_le_a_of_five_mem (n := 1704) (q1 := 5) (q2 := 37) (q3 := 83) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1710 : 5 ≤ a 1710 :=
  five_le_a_of_five_mem (n := 1710) (q1 := 11) (q2 := 13) (q3 := 43) (q4 := 73) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1716 : 5 ≤ a 1716 :=
  five_le_a_of_five_mem (n := 1716) (q1 := 7) (q2 := 17) (q3 := 107) (q4 := 157) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1722 : 5 ≤ a 1722 :=
  five_le_a_of_five_mem (n := 1722) (q1 := 101) (q2 := 109) (q3 := 139) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1728 : 5 ≤ a 1728 :=
  five_le_a_of_five_mem (n := 1728) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 59) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1734 : 5 ≤ a 1734 :=
  five_le_a_of_five_mem (n := 1734) (q1 := 13) (q2 := 67) (q3 := 97) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1740 : 5 ≤ a 1740 :=
  five_le_a_of_five_mem (n := 1740) (q1 := 7) (q2 := 19) (q3 := 43) (q4 := 47) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1746 : 5 ≤ a 1746 :=
  five_le_a_of_five_mem (n := 1746) (q1 := 13) (q2 := 37) (q3 := 127) (q4 := 167) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1752 : 5 ≤ a 1752 :=
  five_le_a_of_five_mem (n := 1752) (q1 := 31) (q2 := 59) (q3 := 181) (q4 := 199) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1758 : 5 ≤ a 1758 :=
  five_le_a_of_five_mem (n := 1758) (q1 := 89) (q2 := 131) (q3 := 149) (q4 := 191) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1764 : 5 ≤ a 1764 :=
  five_le_a_of_five_mem (n := 1764) (q1 := 23) (q2 := 67) (q3 := 97) (q4 := 107) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1770 : 5 ≤ a 1770 :=
  five_le_a_of_five_mem (n := 1770) (q1 := 17) (q2 := 61) (q3 := 101) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1776 : 5 ≤ a 1776 :=
  five_le_a_of_five_mem (n := 1776) (q1 := 113) (q2 := 157) (q3 := 197) (q4 := 223) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1782 : 5 ≤ a 1782 :=
  five_le_a_of_five_mem (n := 1782) (q1 := 5) (q2 := 29) (q3 := 41) (q4 := 89) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1788 : 5 ≤ a 1788 :=
  five_le_a_of_five_mem (n := 1788) (q1 := 79) (q2 := 89) (q3 := 191) (q4 := 229) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1794 : 5 ≤ a 1794 :=
  five_le_a_of_five_mem (n := 1794) (q1 := 7) (q2 := 17) (q3 := 53) (q4 := 73) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1800 : 5 ≤ a 1800 :=
  five_le_a_of_five_mem (n := 1800) (q1 := 11) (q2 := 23) (q3 := 47) (q4 := 67) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1806 : 5 ≤ a 1806 :=
  five_le_a_of_five_mem (n := 1806) (q1 := 5) (q2 := 17) (q3 := 73) (q4 := 83) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1812 : 5 ≤ a 1812 :=
  five_le_a_of_five_mem (n := 1812) (q1 := 11) (q2 := 59) (q3 := 89) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1818 : 5 ≤ a 1818 :=
  five_le_a_of_five_mem (n := 1818) (q1 := 29) (q2 := 59) (q3 := 71) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1824 : 5 ≤ a 1824 :=
  five_le_a_of_five_mem (n := 1824) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1830 : 5 ≤ a 1830 :=
  five_le_a_of_five_mem (n := 1830) (q1 := 41) (q2 := 43) (q3 := 47) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1836 : 5 ≤ a 1836 :=
  five_le_a_of_five_mem (n := 1836) (q1 := 53) (q2 := 113) (q3 := 137) (q4 := 167) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1842 : 5 ≤ a 1842 :=
  five_le_a_of_five_mem (n := 1842) (q1 := 19) (q2 := 31) (q3 := 59) (q4 := 89) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1848 : 5 ≤ a 1848 :=
  five_le_a_of_five_mem (n := 1848) (q1 := 59) (q2 := 101) (q3 := 139) (q4 := 149) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1854 : 5 ≤ a 1854 :=
  five_le_a_of_five_mem (n := 1854) (q1 := 7) (q2 := 23) (q3 := 53) (q4 := 157) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1860 : 5 ≤ a 1860 :=
  five_le_a_of_five_mem (n := 1860) (q1 := 13) (q2 := 29) (q3 := 71) (q4 := 73) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1866 : 5 ≤ a 1866 :=
  five_le_a_of_five_mem (n := 1866) (q1 := 5) (q2 := 83) (q3 := 107) (q4 := 113) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1872 : 5 ≤ a 1872 :=
  five_le_a_of_five_mem (n := 1872) (q1 := 5) (q2 := 41) (q3 := 61) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1878 : 5 ≤ a 1878 :=
  five_le_a_of_five_mem (n := 1878) (q1 := 11) (q2 := 101) (q3 := 211) (q4 := 251) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1884 : 5 ≤ a 1884 :=
  five_le_a_of_five_mem (n := 1884) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 227) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1890 : 5 ≤ a 1890 :=
  five_le_a_of_five_mem (n := 1890) (q1 := 11) (q2 := 17) (q3 := 23) (q4 := 43) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1896 : 5 ≤ a 1896 :=
  five_le_a_of_five_mem (n := 1896) (q1 := 17) (q2 := 107) (q3 := 173) (q4 := 233) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1902 : 5 ≤ a 1902 :=
  five_le_a_of_five_mem (n := 1902) (q1 := 29) (q2 := 31) (q3 := 71) (q4 := 101) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1908 : 5 ≤ a 1908 :=
  five_le_a_of_five_mem (n := 1908) (q1 := 41) (q2 := 131) (q3 := 271) (q4 := 359) (q5 := 449)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1914 : 5 ≤ a 1914 :=
  five_le_a_of_five_mem (n := 1914) (q1 := 37) (q2 := 83) (q3 := 103) (q4 := 113) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1920 : 5 ≤ a 1920 :=
  five_le_a_of_five_mem (n := 1920) (q1 := 13) (q2 := 31) (q3 := 53) (q4 := 59) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1926 : 5 ≤ a 1926 :=
  five_le_a_of_five_mem (n := 1926) (q1 := 47) (q2 := 53) (q3 := 103) (q4 := 137) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1932 : 5 ≤ a 1932 :=
  five_le_a_of_five_mem (n := 1932) (q1 := 19) (q2 := 61) (q3 := 71) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1938 : 5 ≤ a 1938 :=
  five_le_a_of_five_mem (n := 1938) (q1 := 59) (q2 := 61) (q3 := 149) (q4 := 151) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1944 : 5 ≤ a 1944 :=
  five_le_a_of_five_mem (n := 1944) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 83) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1950 : 5 ≤ a 1950 :=
  five_le_a_of_five_mem (n := 1950) (q1 := 37) (q2 := 43) (q3 := 61) (q4 := 79) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1956 : 5 ≤ a 1956 :=
  five_le_a_of_five_mem (n := 1956) (q1 := 23) (q2 := 43) (q3 := 83) (q4 := 173) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1962 : 5 ≤ a 1962 :=
  five_le_a_of_five_mem (n := 1962) (q1 := 11) (q2 := 31) (q3 := 101) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1968 : 5 ≤ a 1968 :=
  five_le_a_of_five_mem (n := 1968) (q1 := 19) (q2 := 61) (q3 := 101) (q4 := 269) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1974 : 5 ≤ a 1974 :=
  five_le_a_of_five_mem (n := 1974) (q1 := 23) (q2 := 43) (q3 := 107) (q4 := 113) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1980 : 5 ≤ a 1980 :=
  five_le_a_of_five_mem (n := 1980) (q1 := 7) (q2 := 31) (q3 := 47) (q4 := 73) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1986 : 5 ≤ a 1986 :=
  five_le_a_of_five_mem (n := 1986) (q1 := 7) (q2 := 13) (q3 := 53) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1992 : 5 ≤ a 1992 :=
  five_le_a_of_five_mem (n := 1992) (q1 := 5) (q2 := 19) (q3 := 61) (q4 := 251) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_1998 : 5 ≤ a 1998 :=
  five_le_a_of_five_mem (n := 1998) (q1 := 5) (q2 := 19) (q3 := 131) (q4 := 239) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2004 : 5 ≤ a 2004 :=
  five_le_a_of_five_mem (n := 2004) (q1 := 7) (q2 := 127) (q3 := 137) (q4 := 157) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2010 : 5 ≤ a 2010 :=
  five_le_a_of_five_mem (n := 2010) (q1 := 7) (q2 := 17) (q3 := 59) (q4 := 79) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2016 : 5 ≤ a 2016 :=
  five_le_a_of_five_mem (n := 2016) (q1 := 13) (q2 := 23) (q3 := 37) (q4 := 67) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2022 : 5 ≤ a 2022 :=
  five_le_a_of_five_mem (n := 2022) (q1 := 5) (q2 := 89) (q3 := 109) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2028 : 5 ≤ a 2028 :=
  five_le_a_of_five_mem (n := 2028) (q1 := 11) (q2 := 41) (q3 := 151) (q4 := 239) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2034 : 5 ≤ a 2034 :=
  five_le_a_of_five_mem (n := 2034) (q1 := 5) (q2 := 47) (q3 := 103) (q4 := 127) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2040 : 5 ≤ a 2040 :=
  five_le_a_of_five_mem (n := 2040) (q1 := 13) (q2 := 23) (q3 := 29) (q4 := 41) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2046 : 5 ≤ a 2046 :=
  five_le_a_of_five_mem (n := 2046) (q1 := 7) (q2 := 17) (q3 := 43) (q4 := 53) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2052 : 5 ≤ a 2052 :=
  five_le_a_of_five_mem (n := 2052) (q1 := 59) (q2 := 79) (q3 := 101) (q4 := 151) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2058 : 5 ≤ a 2058 :=
  five_le_a_of_five_mem (n := 2058) (q1 := 5) (q2 := 29) (q3 := 31) (q4 := 41) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2064 : 5 ≤ a 2064 :=
  five_le_a_of_five_mem (n := 2064) (q1 := 47) (q2 := 67) (q3 := 157) (q4 := 233) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2070 : 5 ≤ a 2070 :=
  five_le_a_of_five_mem (n := 2070) (q1 := 17) (q2 := 41) (q3 := 43) (q4 := 59) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2076 : 5 ≤ a 2076 :=
  five_le_a_of_five_mem (n := 2076) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 37) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2082 : 5 ≤ a 2082 :=
  five_le_a_of_five_mem (n := 2082) (q1 := 29) (q2 := 71) (q3 := 79) (q4 := 131) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2088 : 5 ≤ a 2088 :=
  five_le_a_of_five_mem (n := 2088) (q1 := 181) (q2 := 199) (q3 := 311) (q4 := 379) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2094 : 5 ≤ a 2094 :=
  five_le_a_of_five_mem (n := 2094) (q1 := 5) (q2 := 67) (q3 := 193) (q4 := 263) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2100 : 5 ≤ a 2100 :=
  five_le_a_of_five_mem (n := 2100) (q1 := 11) (q2 := 13) (q3 := 31) (q4 := 37) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2106 : 5 ≤ a 2106 :=
  five_le_a_of_five_mem (n := 2106) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 107) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2112 : 5 ≤ a 2112 :=
  five_le_a_of_five_mem (n := 2112) (q1 := 29) (q2 := 31) (q3 := 101) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2118 : 5 ≤ a 2118 :=
  five_le_a_of_five_mem (n := 2118) (q1 := 19) (q2 := 89) (q3 := 229) (q4 := 239) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2124 : 5 ≤ a 2124 :=
  five_le_a_of_five_mem (n := 2124) (q1 := 13) (q2 := 37) (q3 := 97) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2130 : 5 ≤ a 2130 :=
  five_le_a_of_five_mem (n := 2130) (q1 := 31) (q2 := 113) (q3 := 137) (q4 := 151) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2136 : 5 ≤ a 2136 :=
  five_le_a_of_five_mem (n := 2136) (q1 := 5) (q2 := 7) (q3 := 67) (q4 := 107) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2142 : 5 ≤ a 2142 :=
  five_le_a_of_five_mem (n := 2142) (q1 := 11) (q2 := 61) (q3 := 79) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2148 : 5 ≤ a 2148 :=
  five_le_a_of_five_mem (n := 2148) (q1 := 5) (q2 := 59) (q3 := 149) (q4 := 199) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2154 : 5 ≤ a 2154 :=
  five_le_a_of_five_mem (n := 2154) (q1 := 67) (q2 := 127) (q3 := 157) (q4 := 223) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2160 : 5 ≤ a 2160 :=
  five_le_a_of_five_mem (n := 2160) (q1 := 19) (q2 := 47) (q3 := 61) (q4 := 79) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2166 : 5 ≤ a 2166 :=
  five_le_a_of_five_mem (n := 2166) (q1 := 13) (q2 := 37) (q3 := 103) (q4 := 127) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2172 : 5 ≤ a 2172 :=
  five_le_a_of_five_mem (n := 2172) (q1 := 31) (q2 := 41) (q3 := 109) (q4 := 179) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2178 : 5 ≤ a 2178 :=
  five_le_a_of_five_mem (n := 2178) (q1 := 89) (q2 := 109) (q3 := 179) (q4 := 199) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2184 : 5 ≤ a 2184 :=
  five_le_a_of_five_mem (n := 2184) (q1 := 23) (q2 := 53) (q3 := 97) (q4 := 103) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2190 : 5 ≤ a 2190 :=
  five_le_a_of_five_mem (n := 2190) (q1 := 47) (q2 := 53) (q3 := 61) (q4 := 79) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2196 : 5 ≤ a 2196 :=
  five_le_a_of_five_mem (n := 2196) (q1 := 17) (q2 := 43) (q3 := 97) (q4 := 113) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2202 : 5 ≤ a 2202 :=
  five_le_a_of_five_mem (n := 2202) (q1 := 41) (q2 := 71) (q3 := 139) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2208 : 5 ≤ a 2208 :=
  five_le_a_of_five_mem (n := 2208) (q1 := 5) (q2 := 29) (q3 := 79) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2214 : 5 ≤ a 2214 :=
  five_le_a_of_five_mem (n := 2214) (q1 := 7) (q2 := 53) (q3 := 73) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2220 : 5 ≤ a 2220 :=
  five_le_a_of_five_mem (n := 2220) (q1 := 17) (q2 := 67) (q3 := 89) (q4 := 131) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2226 : 5 ≤ a 2226 :=
  five_le_a_of_five_mem (n := 2226) (q1 := 13) (q2 := 47) (q3 := 83) (q4 := 113) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2232 : 5 ≤ a 2232 :=
  five_le_a_of_five_mem (n := 2232) (q1 := 11) (q2 := 19) (q3 := 79) (q4 := 101) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2238 : 5 ≤ a 2238 :=
  five_le_a_of_five_mem (n := 2238) (q1 := 31) (q2 := 59) (q3 := 101) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2244 : 5 ≤ a 2244 :=
  five_le_a_of_five_mem (n := 2244) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2250 : 5 ≤ a 2250 :=
  five_le_a_of_five_mem (n := 2250) (q1 := 37) (q2 := 43) (q3 := 47) (q4 := 89) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2256 : 5 ≤ a 2256 :=
  five_le_a_of_five_mem (n := 2256) (q1 := 13) (q2 := 17) (q3 := 53) (q4 := 127) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2262 : 5 ≤ a 2262 :=
  five_le_a_of_five_mem (n := 2262) (q1 := 11) (q2 := 19) (q3 := 109) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2268 : 5 ≤ a 2268 :=
  five_le_a_of_five_mem (n := 2268) (q1 := 29) (q2 := 89) (q3 := 131) (q4 := 179) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2274 : 5 ≤ a 2274 :=
  five_le_a_of_five_mem (n := 2274) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2280 : 5 ≤ a 2280 :=
  five_le_a_of_five_mem (n := 2280) (q1 := 7) (q2 := 13) (q3 := 29) (q4 := 59) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2286 : 5 ≤ a 2286 :=
  five_le_a_of_five_mem (n := 2286) (q1 := 47) (q2 := 107) (q3 := 173) (q4 := 257) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2292 : 5 ≤ a 2292 :=
  five_le_a_of_five_mem (n := 2292) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 79) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2298 : 5 ≤ a 2298 :=
  five_le_a_of_five_mem (n := 2298) (q1 := 11) (q2 := 59) (q3 := 281) (q4 := 311) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2304 : 5 ≤ a 2304 :=
  five_le_a_of_five_mem (n := 2304) (q1 := 7) (q2 := 37) (q3 := 53) (q4 := 67) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2310 : 5 ≤ a 2310 :=
  five_le_a_of_five_mem (n := 2310) (q1 := 23) (q2 := 29) (q3 := 37) (q4 := 41) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2316 : 5 ≤ a 2316 :=
  five_le_a_of_five_mem (n := 2316) (q1 := 23) (q2 := 73) (q3 := 227) (q4 := 233) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2322 : 5 ≤ a 2322 :=
  five_le_a_of_five_mem (n := 2322) (q1 := 11) (q2 := 29) (q3 := 71) (q4 := 101) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2328 : 5 ≤ a 2328 :=
  five_le_a_of_five_mem (n := 2328) (q1 := 19) (q2 := 61) (q3 := 89) (q4 := 149) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2334 : 5 ≤ a 2334 :=
  five_le_a_of_five_mem (n := 2334) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 83) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2340 : 5 ≤ a 2340 :=
  five_le_a_of_five_mem (n := 2340) (q1 := 7) (q2 := 31) (q3 := 43) (q4 := 53) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2346 : 5 ≤ a 2346 :=
  five_le_a_of_five_mem (n := 2346) (q1 := 5) (q2 := 37) (q3 := 53) (q4 := 193) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2352 : 5 ≤ a 2352 :=
  five_le_a_of_five_mem (n := 2352) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 59) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2358 : 5 ≤ a 2358 :=
  five_le_a_of_five_mem (n := 2358) (q1 := 19) (q2 := 89) (q3 := 331) (q4 := 409) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2364 : 5 ≤ a 2364 :=
  five_le_a_of_five_mem (n := 2364) (q1 := 7) (q2 := 13) (q3 := 17) (q4 := 53) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2370 : 5 ≤ a 2370 :=
  five_le_a_of_five_mem (n := 2370) (q1 := 13) (q2 := 19) (q3 := 23) (q4 := 29) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2376 : 5 ≤ a 2376 :=
  five_le_a_of_five_mem (n := 2376) (q1 := 5) (q2 := 83) (q3 := 163) (q4 := 173) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2382 : 5 ≤ a 2382 :=
  five_le_a_of_five_mem (n := 2382) (q1 := 11) (q2 := 41) (q3 := 139) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2388 : 5 ≤ a 2388 :=
  five_le_a_of_five_mem (n := 2388) (q1 := 5) (q2 := 11) (q3 := 79) (q4 := 151) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2394 : 5 ≤ a 2394 :=
  five_le_a_of_five_mem (n := 2394) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2400 : 5 ≤ a 2400 :=
  five_le_a_of_five_mem (n := 2400) (q1 := 11) (q2 := 17) (q3 := 23) (q4 := 59) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2406 : 5 ≤ a 2406 :=
  five_le_a_of_five_mem (n := 2406) (q1 := 17) (q2 := 67) (q3 := 97) (q4 := 137) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2412 : 5 ≤ a 2412 :=
  five_le_a_of_five_mem (n := 2412) (q1 := 29) (q2 := 61) (q3 := 131) (q4 := 139) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2418 : 5 ≤ a 2418 :=
  five_le_a_of_five_mem (n := 2418) (q1 := 19) (q2 := 29) (q3 := 41) (q4 := 131) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2424 : 5 ≤ a 2424 :=
  five_le_a_of_five_mem (n := 2424) (q1 := 13) (q2 := 43) (q3 := 53) (q4 := 127) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2430 : 5 ≤ a 2430 :=
  five_le_a_of_five_mem (n := 2430) (q1 := 7) (q2 := 37) (q3 := 47) (q4 := 73) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2436 : 5 ≤ a 2436 :=
  five_le_a_of_five_mem (n := 2436) (q1 := 37) (q2 := 103) (q3 := 197) (q4 := 223) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2442 : 5 ≤ a 2442 :=
  five_le_a_of_five_mem (n := 2442) (q1 := 5) (q2 := 31) (q3 := 61) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2448 : 5 ≤ a 2448 :=
  five_le_a_of_five_mem (n := 2448) (q1 := 11) (q2 := 101) (q3 := 109) (q4 := 211) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2454 : 5 ≤ a 2454 :=
  five_le_a_of_five_mem (n := 2454) (q1 := 13) (q2 := 97) (q3 := 103) (q4 := 167) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2460 : 5 ≤ a 2460 :=
  five_le_a_of_five_mem (n := 2460) (q1 := 13) (q2 := 43) (q3 := 61) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2466 : 5 ≤ a 2466 :=
  five_le_a_of_five_mem (n := 2466) (q1 := 7) (q2 := 73) (q3 := 83) (q4 := 127) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2472 : 5 ≤ a 2472 :=
  five_le_a_of_five_mem (n := 2472) (q1 := 5) (q2 := 31) (q3 := 79) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2478 : 5 ≤ a 2478 :=
  five_le_a_of_five_mem (n := 2478) (q1 := 61) (q2 := 79) (q3 := 101) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2484 : 5 ≤ a 2484 :=
  five_le_a_of_five_mem (n := 2484) (q1 := 37) (q2 := 47) (q3 := 67) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2490 : 5 ≤ a 2490 :=
  five_le_a_of_five_mem (n := 2490) (q1 := 13) (q2 := 31) (q3 := 53) (q4 := 67) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2496 : 5 ≤ a 2496 :=
  five_le_a_of_five_mem (n := 2496) (q1 := 97) (q2 := 113) (q3 := 163) (q4 := 223) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2502 : 5 ≤ a 2502 :=
  five_le_a_of_five_mem (n := 2502) (q1 := 29) (q2 := 131) (q3 := 191) (q4 := 229) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2508 : 5 ≤ a 2508 :=
  five_le_a_of_five_mem (n := 2508) (q1 := 31) (q2 := 41) (q3 := 71) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2514 : 5 ≤ a 2514 :=
  five_le_a_of_five_mem (n := 2514) (q1 := 37) (q2 := 103) (q3 := 157) (q4 := 163) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2520 : 5 ≤ a 2520 :=
  five_le_a_of_five_mem (n := 2520) (q1 := 73) (q2 := 97) (q3 := 127) (q4 := 137) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2526 : 5 ≤ a 2526 :=
  five_le_a_of_five_mem (n := 2526) (q1 := 5) (q2 := 23) (q3 := 53) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2532 : 5 ≤ a 2532 :=
  five_le_a_of_five_mem (n := 2532) (q1 := 11) (q2 := 59) (q3 := 139) (q4 := 151) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2538 : 5 ≤ a 2538 :=
  five_le_a_of_five_mem (n := 2538) (q1 := 71) (q2 := 79) (q3 := 139) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2544 : 5 ≤ a 2544 :=
  five_le_a_of_five_mem (n := 2544) (q1 := 5) (q2 := 13) (q3 := 103) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2550 : 5 ≤ a 2550 :=
  five_le_a_of_five_mem (n := 2550) (q1 := 7) (q2 := 29) (q3 := 83) (q4 := 109) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2556 : 5 ≤ a 2556 :=
  five_le_a_of_five_mem (n := 2556) (q1 := 53) (q2 := 157) (q3 := 163) (q4 := 173) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2562 : 5 ≤ a 2562 :=
  five_le_a_of_five_mem (n := 2562) (q1 := 31) (q2 := 59) (q3 := 151) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2568 : 5 ≤ a 2568 :=
  five_le_a_of_five_mem (n := 2568) (q1 := 11) (q2 := 109) (q3 := 131) (q4 := 151) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2574 : 5 ≤ a 2574 :=
  five_le_a_of_five_mem (n := 2574) (q1 := 17) (q2 := 43) (q3 := 97) (q4 := 137) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2580 : 5 ≤ a 2580 :=
  five_le_a_of_five_mem (n := 2580) (q1 := 29) (q2 := 37) (q3 := 41) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2586 : 5 ≤ a 2586 :=
  five_le_a_of_five_mem (n := 2586) (q1 := 7) (q2 := 47) (q3 := 113) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2592 : 5 ≤ a 2592 :=
  five_le_a_of_five_mem (n := 2592) (q1 := 41) (q2 := 71) (q3 := 199) (q4 := 211) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2598 : 5 ≤ a 2598 :=
  five_le_a_of_five_mem (n := 2598) (q1 := 19) (q2 := 59) (q3 := 131) (q4 := 151) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2604 : 5 ≤ a 2604 :=
  five_le_a_of_five_mem (n := 2604) (q1 := 13) (q2 := 53) (q3 := 73) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2610 : 5 ≤ a 2610 :=
  five_le_a_of_five_mem (n := 2610) (q1 := 53) (q2 := 61) (q3 := 67) (q4 := 79) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2616 : 5 ≤ a 2616 :=
  five_le_a_of_five_mem (n := 2616) (q1 := 67) (q2 := 73) (q3 := 113) (q4 := 227) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2622 : 5 ≤ a 2622 :=
  five_le_a_of_five_mem (n := 2622) (q1 := 71) (q2 := 181) (q3 := 211) (q4 := 229) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2628 : 5 ≤ a 2628 :=
  five_le_a_of_five_mem (n := 2628) (q1 := 19) (q2 := 71) (q3 := 79) (q4 := 191) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2634 : 5 ≤ a 2634 :=
  five_le_a_of_five_mem (n := 2634) (q1 := 13) (q2 := 43) (q3 := 157) (q4 := 167) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2640 : 5 ≤ a 2640 :=
  five_le_a_of_five_mem (n := 2640) (q1 := 7) (q2 := 19) (q3 := 23) (q4 := 31) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2646 : 5 ≤ a 2646 :=
  five_le_a_of_five_mem (n := 2646) (q1 := 13) (q2 := 37) (q3 := 53) (q4 := 67) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2652 : 5 ≤ a 2652 :=
  five_le_a_of_five_mem (n := 2652) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 59) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2658 : 5 ≤ a 2658 :=
  five_le_a_of_five_mem (n := 2658) (q1 := 41) (q2 := 109) (q3 := 199) (q4 := 269) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2664 : 5 ≤ a 2664 :=
  five_le_a_of_five_mem (n := 2664) (q1 := 7) (q2 := 43) (q3 := 47) (q4 := 113) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2670 : 5 ≤ a 2670 :=
  five_le_a_of_five_mem (n := 2670) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 37) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2676 : 5 ≤ a 2676 :=
  five_le_a_of_five_mem (n := 2676) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 127) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2682 : 5 ≤ a 2682 :=
  five_le_a_of_five_mem (n := 2682) (q1 := 5) (q2 := 11) (q3 := 151) (q4 := 179) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2688 : 5 ≤ a 2688 :=
  five_le_a_of_five_mem (n := 2688) (q1 := 5) (q2 := 11) (q3 := 31) (q4 := 41) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2694 : 5 ≤ a 2694 :=
  five_le_a_of_five_mem (n := 2694) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2700 : 5 ≤ a 2700 :=
  five_le_a_of_five_mem (n := 2700) (q1 := 7) (q2 := 11) (q3 := 13) (q4 := 29) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2706 : 5 ≤ a 2706 :=
  five_le_a_of_five_mem (n := 2706) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2712 : 5 ≤ a 2712 :=
  five_le_a_of_five_mem (n := 2712) (q1 := 19) (q2 := 29) (q3 := 41) (q4 := 79) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2718 : 5 ≤ a 2718 :=
  five_le_a_of_five_mem (n := 2718) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2724 : 5 ≤ a 2724 :=
  five_le_a_of_five_mem (n := 2724) (q1 := 5) (q2 := 17) (q3 := 53) (q4 := 67) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2730 : 5 ≤ a 2730 :=
  five_le_a_of_five_mem (n := 2730) (q1 := 11) (q2 := 19) (q3 := 23) (q4 := 37) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2736 : 5 ≤ a 2736 :=
  five_le_a_of_five_mem (n := 2736) (q1 := 5) (q2 := 17) (q3 := 53) (q4 := 233) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2742 : 5 ≤ a 2742 :=
  five_le_a_of_five_mem (n := 2742) (q1 := 11) (q2 := 59) (q3 := 109) (q4 := 211) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2748 : 5 ≤ a 2748 :=
  five_le_a_of_five_mem (n := 2748) (q1 := 19) (q2 := 29) (q3 := 41) (q4 := 71) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2754 : 5 ≤ a 2754 :=
  five_le_a_of_five_mem (n := 2754) (q1 := 13) (q2 := 23) (q3 := 43) (q4 := 47) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2760 : 5 ≤ a 2760 :=
  five_le_a_of_five_mem (n := 2760) (q1 := 7) (q2 := 29) (q3 := 31) (q4 := 41) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2766 : 5 ≤ a 2766 :=
  five_le_a_of_five_mem (n := 2766) (q1 := 37) (q2 := 53) (q3 := 67) (q4 := 173) (q5 := 563)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2772 : 5 ≤ a 2772 :=
  five_le_a_of_five_mem (n := 2772) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2778 : 5 ≤ a 2778 :=
  five_le_a_of_five_mem (n := 2778) (q1 := 11) (q2 := 59) (q3 := 79) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2784 : 5 ≤ a 2784 :=
  five_le_a_of_five_mem (n := 2784) (q1 := 7) (q2 := 17) (q3 := 53) (q4 := 73) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2790 : 5 ≤ a 2790 :=
  five_le_a_of_five_mem (n := 2790) (q1 := 13) (q2 := 61) (q3 := 71) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2796 : 5 ≤ a 2796 :=
  five_le_a_of_five_mem (n := 2796) (q1 := 5) (q2 := 7) (q3 := 47) (q4 := 83) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2802 : 5 ≤ a 2802 :=
  five_le_a_of_five_mem (n := 2802) (q1 := 281) (q2 := 379) (q3 := 419) (q4 := 521) (q5 := 659)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2808 : 5 ≤ a 2808 :=
  five_le_a_of_five_mem (n := 2808) (q1 := 11) (q2 := 79) (q3 := 89) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2814 : 5 ≤ a 2814 :=
  five_le_a_of_five_mem (n := 2814) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2820 : 5 ≤ a 2820 :=
  five_le_a_of_five_mem (n := 2820) (q1 := 17) (q2 := 23) (q3 := 31) (q4 := 67) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2826 : 5 ≤ a 2826 :=
  five_le_a_of_five_mem (n := 2826) (q1 := 7) (q2 := 113) (q3 := 127) (q4 := 137) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2832 : 5 ≤ a 2832 :=
  five_le_a_of_five_mem (n := 2832) (q1 := 29) (q2 := 139) (q3 := 359) (q4 := 421) (q5 := 439)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2838 : 5 ≤ a 2838 :=
  five_le_a_of_five_mem (n := 2838) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 71) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2844 : 5 ≤ a 2844 :=
  five_le_a_of_five_mem (n := 2844) (q1 := 7) (q2 := 43) (q3 := 53) (q4 := 113) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2850 : 5 ≤ a 2850 :=
  five_le_a_of_five_mem (n := 2850) (q1 := 7) (q2 := 47) (q3 := 53) (q4 := 59) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2856 : 5 ≤ a 2856 :=
  five_le_a_of_five_mem (n := 2856) (q1 := 5) (q2 := 23) (q3 := 53) (q4 := 107) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2862 : 5 ≤ a 2862 :=
  five_le_a_of_five_mem (n := 2862) (q1 := 109) (q2 := 149) (q3 := 179) (q4 := 199) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2868 : 5 ≤ a 2868 :=
  five_le_a_of_five_mem (n := 2868) (q1 := 11) (q2 := 71) (q3 := 101) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2874 : 5 ≤ a 2874 :=
  five_le_a_of_five_mem (n := 2874) (q1 := 13) (q2 := 23) (q3 := 83) (q4 := 97) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2880 : 5 ≤ a 2880 :=
  five_le_a_of_five_mem (n := 2880) (q1 := 23) (q2 := 29) (q3 := 37) (q4 := 47) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2886 : 5 ≤ a 2886 :=
  five_le_a_of_five_mem (n := 2886) (q1 := 53) (q2 := 67) (q3 := 83) (q4 := 137) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2892 : 5 ≤ a 2892 :=
  five_le_a_of_five_mem (n := 2892) (q1 := 5) (q2 := 229) (q3 := 271) (q4 := 499) (q5 := 521)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2898 : 5 ≤ a 2898 :=
  five_le_a_of_five_mem (n := 2898) (q1 := 11) (q2 := 19) (q3 := 41) (q4 := 101) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2904 : 5 ≤ a 2904 :=
  five_le_a_of_five_mem (n := 2904) (q1 := 53) (q2 := 67) (q3 := 107) (q4 := 137) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2910 : 5 ≤ a 2910 :=
  five_le_a_of_five_mem (n := 2910) (q1 := 7) (q2 := 53) (q3 := 59) (q4 := 109) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2916 : 5 ≤ a 2916 :=
  five_le_a_of_five_mem (n := 2916) (q1 := 37) (q2 := 83) (q3 := 163) (q4 := 167) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2922 : 5 ≤ a 2922 :=
  five_le_a_of_five_mem (n := 2922) (q1 := 5) (q2 := 79) (q3 := 89) (q4 := 331) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2928 : 5 ≤ a 2928 :=
  five_le_a_of_five_mem (n := 2928) (q1 := 11) (q2 := 41) (q3 := 71) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2934 : 5 ≤ a 2934 :=
  five_le_a_of_five_mem (n := 2934) (q1 := 37) (q2 := 257) (q3 := 317) (q4 := 457) (q5 := 523)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2940 : 5 ≤ a 2940 :=
  five_le_a_of_five_mem (n := 2940) (q1 := 13) (q2 := 23) (q3 := 31) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2946 : 5 ≤ a 2946 :=
  five_le_a_of_five_mem (n := 2946) (q1 := 7) (q2 := 103) (q3 := 257) (q4 := 263) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2952 : 5 ≤ a 2952 :=
  five_le_a_of_five_mem (n := 2952) (q1 := 109) (q2 := 211) (q3 := 239) (q4 := 269) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2958 : 5 ≤ a 2958 :=
  five_le_a_of_five_mem (n := 2958) (q1 := 5) (q2 := 41) (q3 := 61) (q4 := 79) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2964 : 5 ≤ a 2964 :=
  five_le_a_of_five_mem (n := 2964) (q1 := 7) (q2 := 37) (q3 := 47) (q4 := 103) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2970 : 5 ≤ a 2970 :=
  five_le_a_of_five_mem (n := 2970) (q1 := 31) (q2 := 53) (q3 := 67) (q4 := 109) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2976 : 5 ≤ a 2976 :=
  five_le_a_of_five_mem (n := 2976) (q1 := 23) (q2 := 73) (q3 := 227) (q4 := 277) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2982 : 5 ≤ a 2982 :=
  five_le_a_of_five_mem (n := 2982) (q1 := 19) (q2 := 29) (q3 := 79) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2988 : 5 ≤ a 2988 :=
  five_le_a_of_five_mem (n := 2988) (q1 := 31) (q2 := 61) (q3 := 79) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_2994 : 5 ≤ a 2994 :=
  five_le_a_of_five_mem (n := 2994) (q1 := 67) (q2 := 193) (q3 := 197) (q4 := 227) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3000 : 5 ≤ a 3000 :=
  five_le_a_of_five_mem (n := 3000) (q1 := 37) (q2 := 61) (q3 := 83) (q4 := 163) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3006 : 5 ≤ a 3006 :=
  five_le_a_of_five_mem (n := 3006) (q1 := 5) (q2 := 43) (q3 := 103) (q4 := 163) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3012 : 5 ≤ a 3012 :=
  five_le_a_of_five_mem (n := 3012) (q1 := 11) (q2 := 109) (q3 := 151) (q4 := 179) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3018 : 5 ≤ a 3018 :=
  five_le_a_of_five_mem (n := 3018) (q1 := 19) (q2 := 61) (q3 := 101) (q4 := 199) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3024 : 5 ≤ a 3024 :=
  five_le_a_of_five_mem (n := 3024) (q1 := 13) (q2 := 97) (q3 := 163) (q4 := 167) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3030 : 5 ≤ a 3030 :=
  five_le_a_of_five_mem (n := 3030) (q1 := 7) (q2 := 11) (q3 := 19) (q4 := 31) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3036 : 5 ≤ a 3036 :=
  five_le_a_of_five_mem (n := 3036) (q1 := 13) (q2 := 73) (q3 := 83) (q4 := 127) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3042 : 5 ≤ a 3042 :=
  five_le_a_of_five_mem (n := 3042) (q1 := 19) (q2 := 41) (q3 := 79) (q4 := 139) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3048 : 5 ≤ a 3048 :=
  five_le_a_of_five_mem (n := 3048) (q1 := 139) (q2 := 211) (q3 := 251) (q4 := 271) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3054 : 5 ≤ a 3054 :=
  five_le_a_of_five_mem (n := 3054) (q1 := 13) (q2 := 83) (q3 := 127) (q4 := 137) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3060 : 5 ≤ a 3060 :=
  five_le_a_of_five_mem (n := 3060) (q1 := 19) (q2 := 23) (q3 := 59) (q4 := 61) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3066 : 5 ≤ a 3066 :=
  five_le_a_of_five_mem (n := 3066) (q1 := 17) (q2 := 43) (q3 := 97) (q4 := 103) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3072 : 5 ≤ a 3072 :=
  five_le_a_of_five_mem (n := 3072) (q1 := 11) (q2 := 109) (q3 := 229) (q4 := 271) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3078 : 5 ≤ a 3078 :=
  five_le_a_of_five_mem (n := 3078) (q1 := 11) (q2 := 41) (q3 := 59) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3084 : 5 ≤ a 3084 :=
  five_le_a_of_five_mem (n := 3084) (q1 := 5) (q2 := 83) (q3 := 167) (q4 := 223) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3090 : 5 ≤ a 3090 :=
  five_le_a_of_five_mem (n := 3090) (q1 := 29) (q2 := 79) (q3 := 127) (q4 := 163) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3096 : 5 ≤ a 3096 :=
  five_le_a_of_five_mem (n := 3096) (q1 := 13) (q2 := 73) (q3 := 157) (q4 := 263) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3102 : 5 ≤ a 3102 :=
  five_le_a_of_five_mem (n := 3102) (q1 := 19) (q2 := 61) (q3 := 79) (q4 := 101) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3108 : 5 ≤ a 3108 :=
  five_le_a_of_five_mem (n := 3108) (q1 := 29) (q2 := 59) (q3 := 109) (q4 := 151) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3114 : 5 ≤ a 3114 :=
  five_le_a_of_five_mem (n := 3114) (q1 := 5) (q2 := 53) (q3 := 73) (q4 := 103) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3120 : 5 ≤ a 3120 :=
  five_le_a_of_five_mem (n := 3120) (q1 := 71) (q2 := 83) (q3 := 97) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3126 : 5 ≤ a 3126 :=
  five_le_a_of_five_mem (n := 3126) (q1 := 37) (q2 := 43) (q3 := 103) (q4 := 127) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3132 : 5 ≤ a 3132 :=
  five_le_a_of_five_mem (n := 3132) (q1 := 71) (q2 := 229) (q3 := 281) (q4 := 331) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3138 : 5 ≤ a 3138 :=
  five_le_a_of_five_mem (n := 3138) (q1 := 29) (q2 := 71) (q3 := 181) (q4 := 251) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3144 : 5 ≤ a 3144 :=
  five_le_a_of_five_mem (n := 3144) (q1 := 23) (q2 := 107) (q3 := 227) (q4 := 347) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3150 : 5 ≤ a 3150 :=
  five_le_a_of_five_mem (n := 3150) (q1 := 13) (q2 := 31) (q3 := 41) (q4 := 67) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3156 : 5 ≤ a 3156 :=
  five_le_a_of_five_mem (n := 3156) (q1 := 47) (q2 := 73) (q3 := 157) (q4 := 277) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3162 : 5 ≤ a 3162 :=
  five_le_a_of_five_mem (n := 3162) (q1 := 41) (q2 := 139) (q3 := 151) (q4 := 199) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3168 : 5 ≤ a 3168 :=
  five_le_a_of_five_mem (n := 3168) (q1 := 89) (q2 := 131) (q3 := 281) (q4 := 331) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3174 : 5 ≤ a 3174 :=
  five_le_a_of_five_mem (n := 3174) (q1 := 7) (q2 := 173) (q3 := 317) (q4 := 337) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3180 : 5 ≤ a 3180 :=
  five_le_a_of_five_mem (n := 3180) (q1 := 11) (q2 := 71) (q3 := 139) (q4 := 179) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3186 : 5 ≤ a 3186 :=
  five_le_a_of_five_mem (n := 3186) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3192 : 5 ≤ a 3192 :=
  five_le_a_of_five_mem (n := 3192) (q1 := 11) (q2 := 29) (q3 := 109) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3198 : 5 ≤ a 3198 :=
  five_le_a_of_five_mem (n := 3198) (q1 := 11) (q2 := 31) (q3 := 61) (q4 := 109) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3204 : 5 ≤ a 3204 :=
  five_le_a_of_five_mem (n := 3204) (q1 := 13) (q2 := 17) (q3 := 67) (q4 := 167) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3210 : 5 ≤ a 3210 :=
  five_le_a_of_five_mem (n := 3210) (q1 := 7) (q2 := 19) (q3 := 41) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3216 : 5 ≤ a 3216 :=
  five_le_a_of_five_mem (n := 3216) (q1 := 13) (q2 := 97) (q3 := 107) (q4 := 127) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3222 : 5 ≤ a 3222 :=
  five_le_a_of_five_mem (n := 3222) (q1 := 31) (q2 := 101) (q3 := 139) (q4 := 211) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3228 : 5 ≤ a 3228 :=
  five_le_a_of_five_mem (n := 3228) (q1 := 179) (q2 := 229) (q3 := 271) (q4 := 311) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3234 : 5 ≤ a 3234 :=
  five_le_a_of_five_mem (n := 3234) (q1 := 17) (q2 := 67) (q3 := 97) (q4 := 113) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3240 : 5 ≤ a 3240 :=
  five_le_a_of_five_mem (n := 3240) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 59) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3246 : 5 ≤ a 3246 :=
  five_le_a_of_five_mem (n := 3246) (q1 := 83) (q2 := 127) (q3 := 167) (q4 := 223) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3252 : 5 ≤ a 3252 :=
  five_le_a_of_five_mem (n := 3252) (q1 := 61) (q2 := 71) (q3 := 211) (q4 := 281) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3258 : 5 ≤ a 3258 :=
  five_le_a_of_five_mem (n := 3258) (q1 := 41) (q2 := 71) (q3 := 89) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3264 : 5 ≤ a 3264 :=
  five_le_a_of_five_mem (n := 3264) (q1 := 7) (q2 := 43) (q3 := 83) (q4 := 97) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3270 : 5 ≤ a 3270 :=
  five_le_a_of_five_mem (n := 3270) (q1 := 53) (q2 := 61) (q3 := 89) (q4 := 101) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3276 : 5 ≤ a 3276 :=
  five_le_a_of_five_mem (n := 3276) (q1 := 23) (q2 := 47) (q3 := 67) (q4 := 113) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3282 : 5 ≤ a 3282 :=
  five_le_a_of_five_mem (n := 3282) (q1 := 31) (q2 := 61) (q3 := 79) (q4 := 311) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3288 : 5 ≤ a 3288 :=
  five_le_a_of_five_mem (n := 3288) (q1 := 31) (q2 := 59) (q3 := 71) (q4 := 101) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3294 : 5 ≤ a 3294 :=
  five_le_a_of_five_mem (n := 3294) (q1 := 37) (q2 := 113) (q3 := 173) (q4 := 233) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3300 : 5 ≤ a 3300 :=
  five_le_a_of_five_mem (n := 3300) (q1 := 29) (q2 := 43) (q3 := 47) (q4 := 71) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3306 : 5 ≤ a 3306 :=
  five_le_a_of_five_mem (n := 3306) (q1 := 7) (q2 := 53) (q3 := 223) (q4 := 227) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3312 : 5 ≤ a 3312 :=
  five_le_a_of_five_mem (n := 3312) (q1 := 11) (q2 := 59) (q3 := 61) (q4 := 149) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3318 : 5 ≤ a 3318 :=
  five_le_a_of_five_mem (n := 3318) (q1 := 5) (q2 := 11) (q3 := 89) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3324 : 5 ≤ a 3324 :=
  five_le_a_of_five_mem (n := 3324) (q1 := 5) (q2 := 23) (q3 := 67) (q4 := 137) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3330 : 5 ≤ a 3330 :=
  five_le_a_of_five_mem (n := 3330) (q1 := 17) (q2 := 29) (q3 := 31) (q4 := 59) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3336 : 5 ≤ a 3336 :=
  five_le_a_of_five_mem (n := 3336) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 127) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3342 : 5 ≤ a 3342 :=
  five_le_a_of_five_mem (n := 3342) (q1 := 19) (q2 := 29) (q3 := 71) (q4 := 281) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3348 : 5 ≤ a 3348 :=
  five_le_a_of_five_mem (n := 3348) (q1 := 41) (q2 := 179) (q3 := 181) (q4 := 211) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3354 : 5 ≤ a 3354 :=
  five_le_a_of_five_mem (n := 3354) (q1 := 7) (q2 := 53) (q3 := 103) (q4 := 137) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3360 : 5 ≤ a 3360 :=
  five_le_a_of_five_mem (n := 3360) (q1 := 13) (q2 := 29) (q3 := 31) (q4 := 47) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3366 : 5 ≤ a 3366 :=
  five_le_a_of_five_mem (n := 3366) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3372 : 5 ≤ a 3372 :=
  five_le_a_of_five_mem (n := 3372) (q1 := 41) (q2 := 251) (q3 := 571) (q4 := 631) (q5 := 641)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3378 : 5 ≤ a 3378 :=
  five_le_a_of_five_mem (n := 3378) (q1 := 71) (q2 := 79) (q3 := 149) (q4 := 499) (q5 := 541)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3384 : 5 ≤ a 3384 :=
  five_le_a_of_five_mem (n := 3384) (q1 := 23) (q2 := 83) (q3 := 127) (q4 := 163) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3390 : 5 ≤ a 3390 :=
  five_le_a_of_five_mem (n := 3390) (q1 := 17) (q2 := 43) (q3 := 59) (q4 := 67) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3396 : 5 ≤ a 3396 :=
  five_le_a_of_five_mem (n := 3396) (q1 := 37) (q2 := 53) (q3 := 67) (q4 := 73) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3402 : 5 ≤ a 3402 :=
  five_le_a_of_five_mem (n := 3402) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3408 : 5 ≤ a 3408 :=
  five_le_a_of_five_mem (n := 3408) (q1 := 61) (q2 := 109) (q3 := 149) (q4 := 151) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3414 : 5 ≤ a 3414 :=
  five_le_a_of_five_mem (n := 3414) (q1 := 43) (q2 := 53) (q3 := 113) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3420 : 5 ≤ a 3420 :=
  five_le_a_of_five_mem (n := 3420) (q1 := 13) (q2 := 29) (q3 := 47) (q4 := 97) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3426 : 5 ≤ a 3426 :=
  five_le_a_of_five_mem (n := 3426) (q1 := 37) (q2 := 103) (q3 := 107) (q4 := 113) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3432 : 5 ≤ a 3432 :=
  five_le_a_of_five_mem (n := 3432) (q1 := 59) (q2 := 101) (q3 := 109) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3438 : 5 ≤ a 3438 :=
  five_le_a_of_five_mem (n := 3438) (q1 := 31) (q2 := 79) (q3 := 109) (q4 := 179) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3444 : 5 ≤ a 3444 :=
  five_le_a_of_five_mem (n := 3444) (q1 := 73) (q2 := 83) (q3 := 97) (q4 := 113) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3450 : 5 ≤ a 3450 :=
  five_le_a_of_five_mem (n := 3450) (q1 := 17) (q2 := 61) (q3 := 79) (q4 := 89) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3456 : 5 ≤ a 3456 :=
  five_le_a_of_five_mem (n := 3456) (q1 := 7) (q2 := 43) (q3 := 83) (q4 := 127) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3462 : 5 ≤ a 3462 :=
  five_le_a_of_five_mem (n := 3462) (q1 := 5) (q2 := 29) (q3 := 71) (q4 := 131) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3468 : 5 ≤ a 3468 :=
  five_le_a_of_five_mem (n := 3468) (q1 := 61) (q2 := 79) (q3 := 139) (q4 := 149) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3474 : 5 ≤ a 3474 :=
  five_le_a_of_five_mem (n := 3474) (q1 := 17) (q2 := 67) (q3 := 83) (q4 := 223) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3480 : 5 ≤ a 3480 :=
  five_le_a_of_five_mem (n := 3480) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3486 : 5 ≤ a 3486 :=
  five_le_a_of_five_mem (n := 3486) (q1 := 53) (q2 := 73) (q3 := 97) (q4 := 127) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3492 : 5 ≤ a 3492 :=
  five_le_a_of_five_mem (n := 3492) (q1 := 79) (q2 := 101) (q3 := 131) (q4 := 179) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3498 : 5 ≤ a 3498 :=
  five_le_a_of_five_mem (n := 3498) (q1 := 29) (q2 := 31) (q3 := 41) (q4 := 109) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3504 : 5 ≤ a 3504 :=
  five_le_a_of_five_mem (n := 3504) (q1 := 13) (q2 := 37) (q3 := 43) (q4 := 113) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3510 : 5 ≤ a 3510 :=
  five_le_a_of_five_mem (n := 3510) (q1 := 19) (q2 := 47) (q3 := 61) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3516 : 5 ≤ a 3516 :=
  five_le_a_of_five_mem (n := 3516) (q1 := 17) (q2 := 67) (q3 := 127) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3522 : 5 ≤ a 3522 :=
  five_le_a_of_five_mem (n := 3522) (q1 := 5) (q2 := 11) (q3 := 59) (q4 := 61) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3528 : 5 ≤ a 3528 :=
  five_le_a_of_five_mem (n := 3528) (q1 := 11) (q2 := 29) (q3 := 79) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3534 : 5 ≤ a 3534 :=
  five_le_a_of_five_mem (n := 3534) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 73) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3540 : 5 ≤ a 3540 :=
  five_le_a_of_five_mem (n := 3540) (q1 := 7) (q2 := 41) (q3 := 73) (q4 := 83) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3546 : 5 ≤ a 3546 :=
  five_le_a_of_five_mem (n := 3546) (q1 := 13) (q2 := 47) (q3 := 97) (q4 := 113) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3552 : 5 ≤ a 3552 :=
  five_le_a_of_five_mem (n := 3552) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 61) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3558 : 5 ≤ a 3558 :=
  five_le_a_of_five_mem (n := 3558) (q1 := 59) (q2 := 101) (q3 := 151) (q4 := 211) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3564 : 5 ≤ a 3564 :=
  five_le_a_of_five_mem (n := 3564) (q1 := 7) (q2 := 17) (q3 := 53) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3570 : 5 ≤ a 3570 :=
  five_le_a_of_five_mem (n := 3570) (q1 := 11) (q2 := 13) (q3 := 23) (q4 := 37) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3576 : 5 ≤ a 3576 :=
  five_le_a_of_five_mem (n := 3576) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 47) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3582 : 5 ≤ a 3582 :=
  five_le_a_of_five_mem (n := 3582) (q1 := 11) (q2 := 41) (q3 := 211) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3588 : 5 ≤ a 3588 :=
  five_le_a_of_five_mem (n := 3588) (q1 := 5) (q2 := 29) (q3 := 71) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3594 : 5 ≤ a 3594 :=
  five_le_a_of_five_mem (n := 3594) (q1 := 13) (q2 := 23) (q3 := 37) (q4 := 83) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3600 : 5 ≤ a 3600 :=
  five_le_a_of_five_mem (n := 3600) (q1 := 7) (q2 := 17) (q3 := 43) (q4 := 59) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3606 : 5 ≤ a 3606 :=
  five_le_a_of_five_mem (n := 3606) (q1 := 67) (q2 := 173) (q3 := 283) (q4 := 397) (q5 := 443)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3612 : 5 ≤ a 3612 :=
  five_le_a_of_five_mem (n := 3612) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 79) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3618 : 5 ≤ a 3618 :=
  five_le_a_of_five_mem (n := 3618) (q1 := 5) (q2 := 59) (q3 := 79) (q4 := 101) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3624 : 5 ≤ a 3624 :=
  five_le_a_of_five_mem (n := 3624) (q1 := 7) (q2 := 53) (q3 := 67) (q4 := 293) (q5 := 433)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3630 : 5 ≤ a 3630 :=
  five_le_a_of_five_mem (n := 3630) (q1 := 7) (q2 := 13) (q3 := 47) (q4 := 71) (q5 := 89)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3636 : 5 ≤ a 3636 :=
  five_le_a_of_five_mem (n := 3636) (q1 := 23) (q2 := 97) (q3 := 103) (q4 := 167) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3642 : 5 ≤ a 3642 :=
  five_le_a_of_five_mem (n := 3642) (q1 := 29) (q2 := 59) (q3 := 151) (q4 := 179) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3648 : 5 ≤ a 3648 :=
  five_le_a_of_five_mem (n := 3648) (q1 := 11) (q2 := 131) (q3 := 149) (q4 := 199) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3654 : 5 ≤ a 3654 :=
  five_le_a_of_five_mem (n := 3654) (q1 := 17) (q2 := 23) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3660 : 5 ≤ a 3660 :=
  five_le_a_of_five_mem (n := 3660) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 79) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3666 : 5 ≤ a 3666 :=
  five_le_a_of_five_mem (n := 3666) (q1 := 7) (q2 := 43) (q3 := 53) (q4 := 73) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3672 : 5 ≤ a 3672 :=
  five_le_a_of_five_mem (n := 3672) (q1 := 29) (q2 := 89) (q3 := 131) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3678 : 5 ≤ a 3678 :=
  five_le_a_of_five_mem (n := 3678) (q1 := 19) (q2 := 41) (q3 := 61) (q4 := 211) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3684 : 5 ≤ a 3684 :=
  five_le_a_of_five_mem (n := 3684) (q1 := 7) (q2 := 13) (q3 := 113) (q4 := 137) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3690 : 5 ≤ a 3690 :=
  five_le_a_of_five_mem (n := 3690) (q1 := 19) (q2 := 107) (q3 := 131) (q4 := 157) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3696 : 5 ≤ a 3696 :=
  five_le_a_of_five_mem (n := 3696) (q1 := 5) (q2 := 23) (q3 := 37) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3702 : 5 ≤ a 3702 :=
  five_le_a_of_five_mem (n := 3702) (q1 := 31) (q2 := 59) (q3 := 131) (q4 := 241) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3708 : 5 ≤ a 3708 :=
  five_le_a_of_five_mem (n := 3708) (q1 := 11) (q2 := 31) (q3 := 71) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3714 : 5 ≤ a 3714 :=
  five_le_a_of_five_mem (n := 3714) (q1 := 5) (q2 := 13) (q3 := 83) (q4 := 107) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3720 : 5 ≤ a 3720 :=
  five_le_a_of_five_mem (n := 3720) (q1 := 19) (q2 := 47) (q3 := 83) (q4 := 103) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3726 : 5 ≤ a 3726 :=
  five_le_a_of_five_mem (n := 3726) (q1 := 7) (q2 := 53) (q3 := 67) (q4 := 193) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3732 : 5 ≤ a 3732 :=
  five_le_a_of_five_mem (n := 3732) (q1 := 61) (q2 := 89) (q3 := 101) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3738 : 5 ≤ a 3738 :=
  five_le_a_of_five_mem (n := 3738) (q1 := 29) (q2 := 41) (q3 := 179) (q4 := 181) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3744 : 5 ≤ a 3744 :=
  five_le_a_of_five_mem (n := 3744) (q1 := 17) (q2 := 53) (q3 := 107) (q4 := 137) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3750 : 5 ≤ a 3750 :=
  five_le_a_of_five_mem (n := 3750) (q1 := 11) (q2 := 17) (q3 := 53) (q4 := 73) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3756 : 5 ≤ a 3756 :=
  five_le_a_of_five_mem (n := 3756) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 97) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3762 : 5 ≤ a 3762 :=
  five_le_a_of_five_mem (n := 3762) (q1 := 61) (q2 := 71) (q3 := 89) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3768 : 5 ≤ a 3768 :=
  five_le_a_of_five_mem (n := 3768) (q1 := 29) (q2 := 109) (q3 := 151) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3774 : 5 ≤ a 3774 :=
  five_le_a_of_five_mem (n := 3774) (q1 := 5) (q2 := 47) (q3 := 73) (q4 := 103) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3780 : 5 ≤ a 3780 :=
  five_le_a_of_five_mem (n := 3780) (q1 := 13) (q2 := 41) (q3 := 53) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3786 : 5 ≤ a 3786 :=
  five_le_a_of_five_mem (n := 3786) (q1 := 7) (q2 := 17) (q3 := 47) (q4 := 67) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3792 : 5 ≤ a 3792 :=
  five_le_a_of_five_mem (n := 3792) (q1 := 31) (q2 := 59) (q3 := 211) (q4 := 281) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3798 : 5 ≤ a 3798 :=
  five_le_a_of_five_mem (n := 3798) (q1 := 5) (q2 := 79) (q3 := 191) (q4 := 251) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3804 : 5 ≤ a 3804 :=
  five_le_a_of_five_mem (n := 3804) (q1 := 43) (q2 := 103) (q3 := 107) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3810 : 5 ≤ a 3810 :=
  five_le_a_of_five_mem (n := 3810) (q1 := 13) (q2 := 41) (q3 := 43) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3816 : 5 ≤ a 3816 :=
  five_le_a_of_five_mem (n := 3816) (q1 := 37) (q2 := 47) (q3 := 107) (q4 := 173) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3822 : 5 ≤ a 3822 :=
  five_le_a_of_five_mem (n := 3822) (q1 := 29) (q2 := 89) (q3 := 179) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3828 : 5 ≤ a 3828 :=
  five_le_a_of_five_mem (n := 3828) (q1 := 5) (q2 := 61) (q3 := 89) (q4 := 101) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3834 : 5 ≤ a 3834 :=
  five_le_a_of_five_mem (n := 3834) (q1 := 13) (q2 := 73) (q3 := 277) (q4 := 293) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3840 : 5 ≤ a 3840 :=
  five_le_a_of_five_mem (n := 3840) (q1 := 7) (q2 := 37) (q3 := 71) (q4 := 79) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3846 : 5 ≤ a 3846 :=
  five_le_a_of_five_mem (n := 3846) (q1 := 43) (q2 := 173) (q3 := 233) (q4 := 307) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3852 : 5 ≤ a 3852 :=
  five_le_a_of_five_mem (n := 3852) (q1 := 29) (q2 := 59) (q3 := 151) (q4 := 239) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3858 : 5 ≤ a 3858 :=
  five_le_a_of_five_mem (n := 3858) (q1 := 5) (q2 := 61) (q3 := 89) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3864 : 5 ≤ a 3864 :=
  five_le_a_of_five_mem (n := 3864) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 67) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3870 : 5 ≤ a 3870 :=
  five_le_a_of_five_mem (n := 3870) (q1 := 7) (q2 := 19) (q3 := 37) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3876 : 5 ≤ a 3876 :=
  five_le_a_of_five_mem (n := 3876) (q1 := 13) (q2 := 43) (q3 := 53) (q4 := 137) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3882 : 5 ≤ a 3882 :=
  five_le_a_of_five_mem (n := 3882) (q1 := 29) (q2 := 61) (q3 := 191) (q4 := 211) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3888 : 5 ≤ a 3888 :=
  five_le_a_of_five_mem (n := 3888) (q1 := 41) (q2 := 191) (q3 := 211) (q4 := 251) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3894 : 5 ≤ a 3894 :=
  five_le_a_of_five_mem (n := 3894) (q1 := 13) (q2 := 17) (q3 := 73) (q4 := 127) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3900 : 5 ≤ a 3900 :=
  five_le_a_of_five_mem (n := 3900) (q1 := 11) (q2 := 19) (q3 := 23) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3906 : 5 ≤ a 3906 :=
  five_le_a_of_five_mem (n := 3906) (q1 := 17) (q2 := 83) (q3 := 113) (q4 := 167) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3912 : 5 ≤ a 3912 :=
  five_le_a_of_five_mem (n := 3912) (q1 := 5) (q2 := 31) (q3 := 89) (q4 := 109) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3918 : 5 ≤ a 3918 :=
  five_le_a_of_five_mem (n := 3918) (q1 := 11) (q2 := 29) (q3 := 71) (q4 := 139) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3924 : 5 ≤ a 3924 :=
  five_le_a_of_five_mem (n := 3924) (q1 := 5) (q2 := 7) (q3 := 43) (q4 := 103) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3930 : 5 ≤ a 3930 :=
  five_le_a_of_five_mem (n := 3930) (q1 := 13) (q2 := 83) (q3 := 97) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3936 : 5 ≤ a 3936 :=
  five_le_a_of_five_mem (n := 3936) (q1 := 7) (q2 := 83) (q3 := 113) (q4 := 157) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3942 : 5 ≤ a 3942 :=
  five_le_a_of_five_mem (n := 3942) (q1 := 61) (q2 := 79) (q3 := 109) (q4 := 149) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3948 : 5 ≤ a 3948 :=
  five_le_a_of_five_mem (n := 3948) (q1 := 19) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3954 : 5 ≤ a 3954 :=
  five_le_a_of_five_mem (n := 3954) (q1 := 47) (q2 := 73) (q3 := 103) (q4 := 157) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3960 : 5 ≤ a 3960 :=
  five_le_a_of_five_mem (n := 3960) (q1 := 29) (q2 := 41) (q3 := 43) (q4 := 53) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3966 : 5 ≤ a 3966 :=
  five_le_a_of_five_mem (n := 3966) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 113) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3972 : 5 ≤ a 3972 :=
  five_le_a_of_five_mem (n := 3972) (q1 := 29) (q2 := 41) (q3 := 139) (q4 := 239) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3978 : 5 ≤ a 3978 :=
  five_le_a_of_five_mem (n := 3978) (q1 := 11) (q2 := 71) (q3 := 101) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3984 : 5 ≤ a 3984 :=
  five_le_a_of_five_mem (n := 3984) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3990 : 5 ≤ a 3990 :=
  five_le_a_of_five_mem (n := 3990) (q1 := 23) (q2 := 59) (q3 := 61) (q4 := 67) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_3996 : 5 ≤ a 3996 :=
  five_le_a_of_five_mem (n := 3996) (q1 := 7) (q2 := 53) (q3 := 163) (q4 := 257) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4002 : 5 ≤ a 4002 :=
  five_le_a_of_five_mem (n := 4002) (q1 := 71) (q2 := 151) (q3 := 199) (q4 := 241) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4008 : 5 ≤ a 4008 :=
  five_le_a_of_five_mem (n := 4008) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 131) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4014 : 5 ≤ a 4014 :=
  five_le_a_of_five_mem (n := 4014) (q1 := 7) (q2 := 13) (q3 := 97) (q4 := 163) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4020 : 5 ≤ a 4020 :=
  five_le_a_of_five_mem (n := 4020) (q1 := 7) (q2 := 31) (q3 := 53) (q4 := 73) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4026 : 5 ≤ a 4026 :=
  five_le_a_of_five_mem (n := 4026) (q1 := 23) (q2 := 103) (q3 := 107) (q4 := 193) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4032 : 5 ≤ a 4032 :=
  five_le_a_of_five_mem (n := 4032) (q1 := 19) (q2 := 101) (q3 := 179) (q4 := 199) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4038 : 5 ≤ a 4038 :=
  five_le_a_of_five_mem (n := 4038) (q1 := 11) (q2 := 19) (q3 := 191) (q4 := 311) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4044 : 5 ≤ a 4044 :=
  five_le_a_of_five_mem (n := 4044) (q1 := 113) (q2 := 167) (q3 := 197) (q4 := 283) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4050 : 5 ≤ a 4050 :=
  five_le_a_of_five_mem (n := 4050) (q1 := 23) (q2 := 29) (q3 := 43) (q4 := 61) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4056 : 5 ≤ a 4056 :=
  five_le_a_of_five_mem (n := 4056) (q1 := 37) (q2 := 43) (q3 := 233) (q4 := 317) (q5 := 463)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4062 : 5 ≤ a 4062 :=
  five_le_a_of_five_mem (n := 4062) (q1 := 11) (q2 := 139) (q3 := 181) (q4 := 199) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4068 : 5 ≤ a 4068 :=
  five_le_a_of_five_mem (n := 4068) (q1 := 11) (q2 := 61) (q3 := 149) (q4 := 151) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4074 : 5 ≤ a 4074 :=
  five_le_a_of_five_mem (n := 4074) (q1 := 17) (q2 := 53) (q3 := 127) (q4 := 157) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4080 : 5 ≤ a 4080 :=
  five_le_a_of_five_mem (n := 4080) (q1 := 31) (q2 := 53) (q3 := 59) (q4 := 73) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4086 : 5 ≤ a 4086 :=
  five_le_a_of_five_mem (n := 4086) (q1 := 7) (q2 := 13) (q3 := 67) (q4 := 73) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4092 : 5 ≤ a 4092 :=
  five_le_a_of_five_mem (n := 4092) (q1 := 19) (q2 := 41) (q3 := 149) (q4 := 181) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4098 : 5 ≤ a 4098 :=
  five_le_a_of_five_mem (n := 4098) (q1 := 41) (q2 := 79) (q3 := 131) (q4 := 191) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4104 : 5 ≤ a 4104 :=
  five_le_a_of_five_mem (n := 4104) (q1 := 53) (q2 := 97) (q3 := 137) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4110 : 5 ≤ a 4110 :=
  five_le_a_of_five_mem (n := 4110) (q1 := 17) (q2 := 19) (q3 := 107) (q4 := 109) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4116 : 5 ≤ a 4116 :=
  five_le_a_of_five_mem (n := 4116) (q1 := 17) (q2 := 23) (q3 := 37) (q4 := 43) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4122 : 5 ≤ a 4122 :=
  five_le_a_of_five_mem (n := 4122) (q1 := 11) (q2 := 31) (q3 := 109) (q4 := 241) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4128 : 5 ≤ a 4128 :=
  five_le_a_of_five_mem (n := 4128) (q1 := 29) (q2 := 101) (q3 := 199) (q4 := 211) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4134 : 5 ≤ a 4134 :=
  five_le_a_of_five_mem (n := 4134) (q1 := 5) (q2 := 23) (q3 := 43) (q4 := 83) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4140 : 5 ≤ a 4140 :=
  five_le_a_of_five_mem (n := 4140) (q1 := 13) (q2 := 61) (q3 := 89) (q4 := 113) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4146 : 5 ≤ a 4146 :=
  five_le_a_of_five_mem (n := 4146) (q1 := 7) (q2 := 13) (q3 := 73) (q4 := 97) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4152 : 5 ≤ a 4152 :=
  five_le_a_of_five_mem (n := 4152) (q1 := 59) (q2 := 79) (q3 := 101) (q4 := 131) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4158 : 5 ≤ a 4158 :=
  five_le_a_of_five_mem (n := 4158) (q1 := 19) (q2 := 59) (q3 := 101) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4164 : 5 ≤ a 4164 :=
  five_le_a_of_five_mem (n := 4164) (q1 := 37) (q2 := 53) (q3 := 107) (q4 := 163) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4170 : 5 ≤ a 4170 :=
  five_le_a_of_five_mem (n := 4170) (q1 := 31) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4176 : 5 ≤ a 4176 :=
  five_le_a_of_five_mem (n := 4176) (q1 := 43) (q2 := 83) (q3 := 97) (q4 := 163) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4182 : 5 ≤ a 4182 :=
  five_le_a_of_five_mem (n := 4182) (q1 := 29) (q2 := 71) (q3 := 89) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4188 : 5 ≤ a 4188 :=
  five_le_a_of_five_mem (n := 4188) (q1 := 29) (q2 := 31) (q3 := 109) (q4 := 139) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4194 : 5 ≤ a 4194 :=
  five_le_a_of_five_mem (n := 4194) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 103) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4200 : 5 ≤ a 4200 :=
  five_le_a_of_five_mem (n := 4200) (q1 := 41) (q2 := 43) (q3 := 61) (q4 := 71) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4206 : 5 ≤ a 4206 :=
  five_le_a_of_five_mem (n := 4206) (q1 := 5) (q2 := 47) (q3 := 53) (q4 := 67) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4212 : 5 ≤ a 4212 :=
  five_le_a_of_five_mem (n := 4212) (q1 := 59) (q2 := 211) (q3 := 269) (q4 := 281) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4218 : 5 ≤ a 4218 :=
  five_le_a_of_five_mem (n := 4218) (q1 := 41) (q2 := 79) (q3 := 139) (q4 := 191) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4224 : 5 ≤ a 4224 :=
  five_le_a_of_five_mem (n := 4224) (q1 := 5) (q2 := 7) (q3 := 47) (q4 := 113) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4230 : 5 ≤ a 4230 :=
  five_le_a_of_five_mem (n := 4230) (q1 := 11) (q2 := 13) (q3 := 29) (q4 := 53) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4236 : 5 ≤ a 4236 :=
  five_le_a_of_five_mem (n := 4236) (q1 := 5) (q2 := 7) (q3 := 17) (q4 := 103) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4242 : 5 ≤ a 4242 :=
  five_le_a_of_five_mem (n := 4242) (q1 := 11) (q2 := 31) (q3 := 41) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4248 : 5 ≤ a 4248 :=
  five_le_a_of_five_mem (n := 4248) (q1 := 5) (q2 := 89) (q3 := 109) (q4 := 149) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4254 : 5 ≤ a 4254 :=
  five_le_a_of_five_mem (n := 4254) (q1 := 43) (q2 := 197) (q3 := 227) (q4 := 307) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4260 : 5 ≤ a 4260 :=
  five_le_a_of_five_mem (n := 4260) (q1 := 29) (q2 := 103) (q3 := 131) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4266 : 5 ≤ a 4266 :=
  five_le_a_of_five_mem (n := 4266) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 107) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4272 : 5 ≤ a 4272 :=
  five_le_a_of_five_mem (n := 4272) (q1 := 11) (q2 := 179) (q3 := 251) (q4 := 349) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4278 : 5 ≤ a 4278 :=
  five_le_a_of_five_mem (n := 4278) (q1 := 5) (q2 := 19) (q3 := 59) (q4 := 61) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4284 : 5 ≤ a 4284 :=
  five_le_a_of_five_mem (n := 4284) (q1 := 13) (q2 := 43) (q3 := 53) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4290 : 5 ≤ a 4290 :=
  five_le_a_of_five_mem (n := 4290) (q1 := 7) (q2 := 37) (q3 := 47) (q4 := 59) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4296 : 5 ≤ a 4296 :=
  five_le_a_of_five_mem (n := 4296) (q1 := 43) (q2 := 53) (q3 := 67) (q4 := 167) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4302 : 5 ≤ a 4302 :=
  five_le_a_of_five_mem (n := 4302) (q1 := 61) (q2 := 71) (q3 := 149) (q4 := 191) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4308 : 5 ≤ a 4308 :=
  five_le_a_of_five_mem (n := 4308) (q1 := 19) (q2 := 89) (q3 := 149) (q4 := 569) (q5 := 691)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4314 : 5 ≤ a 4314 :=
  five_le_a_of_five_mem (n := 4314) (q1 := 43) (q2 := 83) (q3 := 137) (q4 := 307) (q5 := 547)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4320 : 5 ≤ a 4320 :=
  five_le_a_of_five_mem (n := 4320) (q1 := 37) (q2 := 89) (q3 := 101) (q4 := 103) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4326 : 5 ≤ a 4326 :=
  five_le_a_of_five_mem (n := 4326) (q1 := 37) (q2 := 83) (q3 := 97) (q4 := 167) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4332 : 5 ≤ a 4332 :=
  five_le_a_of_five_mem (n := 4332) (q1 := 5) (q2 := 59) (q3 := 89) (q4 := 131) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4338 : 5 ≤ a 4338 :=
  five_le_a_of_five_mem (n := 4338) (q1 := 11) (q2 := 109) (q3 := 179) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4344 : 5 ≤ a 4344 :=
  five_le_a_of_five_mem (n := 4344) (q1 := 5) (q2 := 47) (q3 := 103) (q4 := 113) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4350 : 5 ≤ a 4350 :=
  five_le_a_of_five_mem (n := 4350) (q1 := 13) (q2 := 23) (q3 := 97) (q4 := 107) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4356 : 5 ≤ a 4356 :=
  five_le_a_of_five_mem (n := 4356) (q1 := 7) (q2 := 17) (q3 := 67) (q4 := 127) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4362 : 5 ≤ a 4362 :=
  five_le_a_of_five_mem (n := 4362) (q1 := 79) (q2 := 89) (q3 := 101) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4368 : 5 ≤ a 4368 :=
  five_le_a_of_five_mem (n := 4368) (q1 := 5) (q2 := 29) (q3 := 41) (q4 := 79) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4374 : 5 ≤ a 4374 :=
  five_le_a_of_five_mem (n := 4374) (q1 := 17) (q2 := 47) (q3 := 173) (q4 := 263) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4380 : 5 ≤ a 4380 :=
  five_le_a_of_five_mem (n := 4380) (q1 := 17) (q2 := 41) (q3 := 43) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4386 : 5 ≤ a 4386 :=
  five_le_a_of_five_mem (n := 4386) (q1 := 23) (q2 := 37) (q3 := 97) (q4 := 127) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4392 : 5 ≤ a 4392 :=
  five_le_a_of_five_mem (n := 4392) (q1 := 29) (q2 := 131) (q3 := 191) (q4 := 281) (q5 := 541)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4398 : 5 ≤ a 4398 :=
  five_le_a_of_five_mem (n := 4398) (q1 := 59) (q2 := 109) (q3 := 239) (q4 := 241) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4404 : 5 ≤ a 4404 :=
  five_le_a_of_five_mem (n := 4404) (q1 := 47) (q2 := 163) (q3 := 193) (q4 := 347) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4410 : 5 ≤ a 4410 :=
  five_le_a_of_five_mem (n := 4410) (q1 := 13) (q2 := 37) (q3 := 47) (q4 := 53) (q5 := 71)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4416 : 5 ≤ a 4416 :=
  five_le_a_of_five_mem (n := 4416) (q1 := 7) (q2 := 67) (q3 := 257) (q4 := 263) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4422 : 5 ≤ a 4422 :=
  five_le_a_of_five_mem (n := 4422) (q1 := 59) (q2 := 139) (q3 := 181) (q4 := 269) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4428 : 5 ≤ a 4428 :=
  five_le_a_of_five_mem (n := 4428) (q1 := 19) (q2 := 79) (q3 := 89) (q4 := 139) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4434 : 5 ≤ a 4434 :=
  five_le_a_of_five_mem (n := 4434) (q1 := 13) (q2 := 163) (q3 := 223) (q4 := 257) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4440 : 5 ≤ a 4440 :=
  five_le_a_of_five_mem (n := 4440) (q1 := 17) (q2 := 43) (q3 := 67) (q4 := 83) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4446 : 5 ≤ a 4446 :=
  five_le_a_of_five_mem (n := 4446) (q1 := 5) (q2 := 37) (q3 := 73) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4452 : 5 ≤ a 4452 :=
  five_le_a_of_five_mem (n := 4452) (q1 := 5) (q2 := 11) (q3 := 29) (q4 := 31) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4458 : 5 ≤ a 4458 :=
  five_le_a_of_five_mem (n := 4458) (q1 := 61) (q2 := 109) (q3 := 199) (q4 := 331) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4464 : 5 ≤ a 4464 :=
  five_le_a_of_five_mem (n := 4464) (q1 := 17) (q2 := 43) (q3 := 127) (q4 := 193) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4470 : 5 ≤ a 4470 :=
  five_le_a_of_five_mem (n := 4470) (q1 := 13) (q2 := 23) (q3 := 47) (q4 := 79) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4476 : 5 ≤ a 4476 :=
  five_le_a_of_five_mem (n := 4476) (q1 := 127) (q2 := 257) (q3 := 317) (q4 := 337) (q5 := 457)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4482 : 5 ≤ a 4482 :=
  five_le_a_of_five_mem (n := 4482) (q1 := 31) (q2 := 41) (q3 := 109) (q4 := 239) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4488 : 5 ≤ a 4488 :=
  five_le_a_of_five_mem (n := 4488) (q1 := 5) (q2 := 31) (q3 := 79) (q4 := 149) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4494 : 5 ≤ a 4494 :=
  five_le_a_of_five_mem (n := 4494) (q1 := 13) (q2 := 53) (q3 := 73) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4500 : 5 ≤ a 4500 :=
  five_le_a_of_five_mem (n := 4500) (q1 := 7) (q2 := 17) (q3 := 19) (q4 := 103) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4506 : 5 ≤ a 4506 :=
  five_le_a_of_five_mem (n := 4506) (q1 := 13) (q2 := 43) (q3 := 97) (q4 := 157) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4512 : 5 ≤ a 4512 :=
  five_le_a_of_five_mem (n := 4512) (q1 := 5) (q2 := 71) (q3 := 139) (q4 := 239) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4518 : 5 ≤ a 4518 :=
  five_le_a_of_five_mem (n := 4518) (q1 := 5) (q2 := 359) (q3 := 419) (q4 := 439) (q5 := 491)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4524 : 5 ≤ a 4524 :=
  five_le_a_of_five_mem (n := 4524) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 127) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4530 : 5 ≤ a 4530 :=
  five_le_a_of_five_mem (n := 4530) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 73) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4536 : 5 ≤ a 4536 :=
  five_le_a_of_five_mem (n := 4536) (q1 := 13) (q2 := 113) (q3 := 127) (q4 := 197) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4542 : 5 ≤ a 4542 :=
  five_le_a_of_five_mem (n := 4542) (q1 := 19) (q2 := 61) (q3 := 79) (q4 := 101) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4548 : 5 ≤ a 4548 :=
  five_le_a_of_five_mem (n := 4548) (q1 := 101) (q2 := 211) (q3 := 251) (q4 := 389) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4554 : 5 ≤ a 4554 :=
  five_le_a_of_five_mem (n := 4554) (q1 := 7) (q2 := 37) (q3 := 97) (q4 := 103) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4560 : 5 ≤ a 4560 :=
  five_le_a_of_five_mem (n := 4560) (q1 := 37) (q2 := 43) (q3 := 79) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4566 : 5 ≤ a 4566 :=
  five_le_a_of_five_mem (n := 4566) (q1 := 17) (q2 := 73) (q3 := 83) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4572 : 5 ≤ a 4572 :=
  five_le_a_of_five_mem (n := 4572) (q1 := 11) (q2 := 79) (q3 := 131) (q4 := 149) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4578 : 5 ≤ a 4578 :=
  five_le_a_of_five_mem (n := 4578) (q1 := 59) (q2 := 61) (q3 := 71) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4584 : 5 ≤ a 4584 :=
  five_le_a_of_five_mem (n := 4584) (q1 := 37) (q2 := 67) (q3 := 137) (q4 := 353) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4590 : 5 ≤ a 4590 :=
  five_le_a_of_five_mem (n := 4590) (q1 := 7) (q2 := 67) (q3 := 73) (q4 := 83) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4596 : 5 ≤ a 4596 :=
  five_le_a_of_five_mem (n := 4596) (q1 := 47) (q2 := 83) (q3 := 307) (q4 := 313) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4602 : 5 ≤ a 4602 :=
  five_le_a_of_five_mem (n := 4602) (q1 := 19) (q2 := 41) (q3 := 89) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4608 : 5 ≤ a 4608 :=
  five_le_a_of_five_mem (n := 4608) (q1 := 41) (q2 := 151) (q3 := 269) (q4 := 281) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4614 : 5 ≤ a 4614 :=
  five_le_a_of_five_mem (n := 4614) (q1 := 23) (q2 := 107) (q3 := 173) (q4 := 257) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4620 : 5 ≤ a 4620 :=
  five_le_a_of_five_mem (n := 4620) (q1 := 17) (q2 := 23) (q3 := 29) (q4 := 37) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4626 : 5 ≤ a 4626 :=
  five_le_a_of_five_mem (n := 4626) (q1 := 23) (q2 := 103) (q3 := 107) (q4 := 163) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4632 : 5 ≤ a 4632 :=
  five_le_a_of_five_mem (n := 4632) (q1 := 11) (q2 := 41) (q3 := 71) (q4 := 151) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4638 : 5 ≤ a 4638 :=
  five_le_a_of_five_mem (n := 4638) (q1 := 41) (q2 := 281) (q3 := 349) (q4 := 421) (q5 := 461)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4644 : 5 ≤ a 4644 :=
  five_le_a_of_five_mem (n := 4644) (q1 := 5) (q2 := 7) (q3 := 47) (q4 := 307) (q5 := 433)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4650 : 5 ≤ a 4650 :=
  five_le_a_of_five_mem (n := 4650) (q1 := 7) (q2 := 13) (q3 := 29) (q4 := 53) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4656 : 5 ≤ a 4656 :=
  five_le_a_of_five_mem (n := 4656) (q1 := 7) (q2 := 17) (q3 := 73) (q4 := 137) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4662 : 5 ≤ a 4662 :=
  five_le_a_of_five_mem (n := 4662) (q1 := 11) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4668 : 5 ≤ a 4668 :=
  five_le_a_of_five_mem (n := 4668) (q1 := 5) (q2 := 11) (q3 := 149) (q4 := 331) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4674 : 5 ≤ a 4674 :=
  five_le_a_of_five_mem (n := 4674) (q1 := 17) (q2 := 113) (q3 := 127) (q4 := 157) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4680 : 5 ≤ a 4680 :=
  five_le_a_of_five_mem (n := 4680) (q1 := 23) (q2 := 41) (q3 := 43) (q4 := 113) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4686 : 5 ≤ a 4686 :=
  five_le_a_of_five_mem (n := 4686) (q1 := 37) (q2 := 43) (q3 := 47) (q4 := 103) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4692 : 5 ≤ a 4692 :=
  five_le_a_of_five_mem (n := 4692) (q1 := 29) (q2 := 41) (q3 := 101) (q4 := 109) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4698 : 5 ≤ a 4698 :=
  five_le_a_of_five_mem (n := 4698) (q1 := 61) (q2 := 101) (q3 := 179) (q4 := 191) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4704 : 5 ≤ a 4704 :=
  five_le_a_of_five_mem (n := 4704) (q1 := 47) (q2 := 83) (q3 := 113) (q4 := 157) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4710 : 5 ≤ a 4710 :=
  five_le_a_of_five_mem (n := 4710) (q1 := 19) (q2 := 73) (q3 := 89) (q4 := 107) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4716 : 5 ≤ a 4716 :=
  five_le_a_of_five_mem (n := 4716) (q1 := 13) (q2 := 43) (q3 := 67) (q4 := 73) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4722 : 5 ≤ a 4722 :=
  five_le_a_of_five_mem (n := 4722) (q1 := 71) (q2 := 79) (q3 := 139) (q4 := 229) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4728 : 5 ≤ a 4728 :=
  five_le_a_of_five_mem (n := 4728) (q1 := 5) (q2 := 71) (q3 := 89) (q4 := 181) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4734 : 5 ≤ a 4734 :=
  five_le_a_of_five_mem (n := 4734) (q1 := 83) (q2 := 97) (q3 := 137) (q4 := 277) (q5 := 463)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4740 : 5 ≤ a 4740 :=
  five_le_a_of_five_mem (n := 4740) (q1 := 11) (q2 := 19) (q3 := 61) (q4 := 137) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4746 : 5 ≤ a 4746 :=
  five_le_a_of_five_mem (n := 4746) (q1 := 13) (q2 := 43) (q3 := 67) (q4 := 163) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4752 : 5 ≤ a 4752 :=
  five_le_a_of_five_mem (n := 4752) (q1 := 31) (q2 := 61) (q3 := 79) (q4 := 109) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4758 : 5 ≤ a 4758 :=
  five_le_a_of_five_mem (n := 4758) (q1 := 29) (q2 := 211) (q3 := 241) (q4 := 251) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4764 : 5 ≤ a 4764 :=
  five_le_a_of_five_mem (n := 4764) (q1 := 107) (q2 := 113) (q3 := 167) (q4 := 173) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4770 : 5 ≤ a 4770 :=
  five_le_a_of_five_mem (n := 4770) (q1 := 19) (q2 := 47) (q3 := 107) (q4 := 149) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4776 : 5 ≤ a 4776 :=
  five_le_a_of_five_mem (n := 4776) (q1 := 17) (q2 := 113) (q3 := 127) (q4 := 193) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4782 : 5 ≤ a 4782 :=
  five_le_a_of_five_mem (n := 4782) (q1 := 31) (q2 := 79) (q3 := 191) (q4 := 269) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4788 : 5 ≤ a 4788 :=
  five_le_a_of_five_mem (n := 4788) (q1 := 5) (q2 := 29) (q3 := 131) (q4 := 149) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4794 : 5 ≤ a 4794 :=
  five_le_a_of_five_mem (n := 4794) (q1 := 5) (q2 := 7) (q3 := 137) (q4 := 157) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4800 : 5 ≤ a 4800 :=
  five_le_a_of_five_mem (n := 4800) (q1 := 13) (q2 := 17) (q3 := 71) (q4 := 109) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4806 : 5 ≤ a 4806 :=
  five_le_a_of_five_mem (n := 4806) (q1 := 7) (q2 := 83) (q3 := 103) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4812 : 5 ≤ a 4812 :=
  five_le_a_of_five_mem (n := 4812) (q1 := 19) (q2 := 139) (q3 := 191) (q4 := 421) (q5 := 449)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4818 : 5 ≤ a 4818 :=
  five_le_a_of_five_mem (n := 4818) (q1 := 59) (q2 := 139) (q3 := 181) (q4 := 269) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4824 : 5 ≤ a 4824 :=
  five_le_a_of_five_mem (n := 4824) (q1 := 7) (q2 := 37) (q3 := 227) (q4 := 257) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4830 : 5 ≤ a 4830 :=
  five_le_a_of_five_mem (n := 4830) (q1 := 31) (q2 := 41) (q3 := 47) (q4 := 79) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4836 : 5 ≤ a 4836 :=
  five_le_a_of_five_mem (n := 4836) (q1 := 53) (q2 := 107) (q3 := 157) (q4 := 163) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4842 : 5 ≤ a 4842 :=
  five_le_a_of_five_mem (n := 4842) (q1 := 29) (q2 := 109) (q3 := 151) (q4 := 179) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4848 : 5 ≤ a 4848 :=
  five_le_a_of_five_mem (n := 4848) (q1 := 61) (q2 := 89) (q3 := 191) (q4 := 211) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4854 : 5 ≤ a 4854 :=
  five_le_a_of_five_mem (n := 4854) (q1 := 23) (q2 := 103) (q3 := 197) (q4 := 233) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4860 : 5 ≤ a 4860 :=
  five_le_a_of_five_mem (n := 4860) (q1 := 29) (q2 := 43) (q3 := 59) (q4 := 71) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4866 : 5 ≤ a 4866 :=
  five_le_a_of_five_mem (n := 4866) (q1 := 5) (q2 := 53) (q3 := 67) (q4 := 107) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4872 : 5 ≤ a 4872 :=
  five_le_a_of_five_mem (n := 4872) (q1 := 59) (q2 := 71) (q3 := 79) (q4 := 139) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4878 : 5 ≤ a 4878 :=
  five_le_a_of_five_mem (n := 4878) (q1 := 79) (q2 := 89) (q3 := 199) (q4 := 229) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4884 : 5 ≤ a 4884 :=
  five_le_a_of_five_mem (n := 4884) (q1 := 53) (q2 := 67) (q3 := 83) (q4 := 193) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4890 : 5 ≤ a 4890 :=
  five_le_a_of_five_mem (n := 4890) (q1 := 13) (q2 := 19) (q3 := 29) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4896 : 5 ≤ a 4896 :=
  five_le_a_of_five_mem (n := 4896) (q1 := 7) (q2 := 97) (q3 := 103) (q4 := 107) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4902 : 5 ≤ a 4902 :=
  five_le_a_of_five_mem (n := 4902) (q1 := 31) (q2 := 41) (q3 := 71) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4908 : 5 ≤ a 4908 :=
  five_le_a_of_five_mem (n := 4908) (q1 := 179) (q2 := 271) (q3 := 389) (q4 := 401) (q5 := 499)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4914 : 5 ≤ a 4914 :=
  five_le_a_of_five_mem (n := 4914) (q1 := 5) (q2 := 37) (q3 := 43) (q4 := 53) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4920 : 5 ≤ a 4920 :=
  five_le_a_of_five_mem (n := 4920) (q1 := 11) (q2 := 17) (q3 := 31) (q4 := 89) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4926 : 5 ≤ a 4926 :=
  five_le_a_of_five_mem (n := 4926) (q1 := 7) (q2 := 17) (q3 := 113) (q4 := 193) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4932 : 5 ≤ a 4932 :=
  five_le_a_of_five_mem (n := 4932) (q1 := 61) (q2 := 71) (q3 := 149) (q4 := 181) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4938 : 5 ≤ a 4938 :=
  five_le_a_of_five_mem (n := 4938) (q1 := 5) (q2 := 19) (q3 := 29) (q4 := 61) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4944 : 5 ≤ a 4944 :=
  five_le_a_of_five_mem (n := 4944) (q1 := 7) (q2 := 13) (q3 := 67) (q4 := 157) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4950 : 5 ≤ a 4950 :=
  five_le_a_of_five_mem (n := 4950) (q1 := 7) (q2 := 17) (q3 := 19) (q4 := 61) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4956 : 5 ≤ a 4956 :=
  five_le_a_of_five_mem (n := 4956) (q1 := 13) (q2 := 37) (q3 := 47) (q4 := 53) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4962 : 5 ≤ a 4962 :=
  five_le_a_of_five_mem (n := 4962) (q1 := 5) (q2 := 11) (q3 := 31) (q4 := 59) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4968 : 5 ≤ a 4968 :=
  five_le_a_of_five_mem (n := 4968) (q1 := 31) (q2 := 151) (q3 := 179) (q4 := 311) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4974 : 5 ≤ a 4974 :=
  five_le_a_of_five_mem (n := 4974) (q1 := 37) (q2 := 103) (q3 := 113) (q4 := 173) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4980 : 5 ≤ a 4980 :=
  five_le_a_of_five_mem (n := 4980) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 29) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4986 : 5 ≤ a 4986 :=
  five_le_a_of_five_mem (n := 4986) (q1 := 13) (q2 := 17) (q3 := 53) (q4 := 193) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4992 : 5 ≤ a 4992 :=
  five_le_a_of_five_mem (n := 4992) (q1 := 19) (q2 := 59) (q3 := 89) (q4 := 179) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_4998 : 5 ≤ a 4998 :=
  five_le_a_of_five_mem (n := 4998) (q1 := 5) (q2 := 11) (q3 := 41) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5004 : 5 ≤ a 5004 :=
  five_le_a_of_five_mem (n := 5004) (q1 := 5) (q2 := 17) (q3 := 47) (q4 := 73) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5010 : 5 ≤ a 5010 :=
  five_le_a_of_five_mem (n := 5010) (q1 := 11) (q2 := 41) (q3 := 67) (q4 := 179) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5016 : 5 ≤ a 5016 :=
  five_le_a_of_five_mem (n := 5016) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 43) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5022 : 5 ≤ a 5022 :=
  five_le_a_of_five_mem (n := 5022) (q1 := 29) (q2 := 79) (q3 := 239) (q4 := 359) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5028 : 5 ≤ a 5028 :=
  five_le_a_of_five_mem (n := 5028) (q1 := 59) (q2 := 71) (q3 := 139) (q4 := 151) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5034 : 5 ≤ a 5034 :=
  five_le_a_of_five_mem (n := 5034) (q1 := 47) (q2 := 67) (q3 := 163) (q4 := 313) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5040 : 5 ≤ a 5040 :=
  five_le_a_of_five_mem (n := 5040) (q1 := 19) (q2 := 37) (q3 := 41) (q4 := 47) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5046 : 5 ≤ a 5046 :=
  five_le_a_of_five_mem (n := 5046) (q1 := 53) (q2 := 73) (q3 := 233) (q4 := 257) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5052 : 5 ≤ a 5052 :=
  five_le_a_of_five_mem (n := 5052) (q1 := 29) (q2 := 101) (q3 := 181) (q4 := 251) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5058 : 5 ≤ a 5058 :=
  five_le_a_of_five_mem (n := 5058) (q1 := 19) (q2 := 89) (q3 := 139) (q4 := 379) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5064 : 5 ≤ a 5064 :=
  five_le_a_of_five_mem (n := 5064) (q1 := 13) (q2 := 43) (q3 := 107) (q4 := 233) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5070 : 5 ≤ a 5070 :=
  five_le_a_of_five_mem (n := 5070) (q1 := 11) (q2 := 31) (q3 := 83) (q4 := 97) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5076 : 5 ≤ a 5076 :=
  five_le_a_of_five_mem (n := 5076) (q1 := 37) (q2 := 103) (q3 := 157) (q4 := 317) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5082 : 5 ≤ a 5082 :=
  five_le_a_of_five_mem (n := 5082) (q1 := 5) (q2 := 31) (q3 := 71) (q4 := 89) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5088 : 5 ≤ a 5088 :=
  five_le_a_of_five_mem (n := 5088) (q1 := 11) (q2 := 79) (q3 := 101) (q4 := 431) (q5 := 439)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5094 : 5 ≤ a 5094 :=
  five_le_a_of_five_mem (n := 5094) (q1 := 7) (q2 := 13) (q3 := 73) (q4 := 137) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5100 : 5 ≤ a 5100 :=
  five_le_a_of_five_mem (n := 5100) (q1 := 13) (q2 := 19) (q3 := 79) (q4 := 89) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5106 : 5 ≤ a 5106 :=
  five_le_a_of_five_mem (n := 5106) (q1 := 7) (q2 := 47) (q3 := 83) (q4 := 103) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5112 : 5 ≤ a 5112 :=
  five_le_a_of_five_mem (n := 5112) (q1 := 281) (q2 := 389) (q3 := 409) (q4 := 461) (q5 := 599)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5118 : 5 ≤ a 5118 :=
  five_le_a_of_five_mem (n := 5118) (q1 := 79) (q2 := 109) (q3 := 229) (q4 := 331) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5124 : 5 ≤ a 5124 :=
  five_le_a_of_five_mem (n := 5124) (q1 := 23) (q2 := 43) (q3 := 47) (q4 := 73) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5130 : 5 ≤ a 5130 :=
  five_le_a_of_five_mem (n := 5130) (q1 := 17) (q2 := 23) (q3 := 79) (q4 := 107) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5136 : 5 ≤ a 5136 :=
  five_le_a_of_five_mem (n := 5136) (q1 := 17) (q2 := 97) (q3 := 137) (q4 := 167) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5142 : 5 ≤ a 5142 :=
  five_le_a_of_five_mem (n := 5142) (q1 := 29) (q2 := 131) (q3 := 139) (q4 := 191) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5148 : 5 ≤ a 5148 :=
  five_le_a_of_five_mem (n := 5148) (q1 := 41) (q2 := 61) (q3 := 89) (q4 := 149) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5154 : 5 ≤ a 5154 :=
  five_le_a_of_five_mem (n := 5154) (q1 := 73) (q2 := 197) (q3 := 277) (q4 := 283) (q5 := 353)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5160 : 5 ≤ a 5160 :=
  five_le_a_of_five_mem (n := 5160) (q1 := 7) (q2 := 73) (q3 := 101) (q4 := 137) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5166 : 5 ≤ a 5166 :=
  five_le_a_of_five_mem (n := 5166) (q1 := 13) (q2 := 67) (q3 := 107) (q4 := 157) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5172 : 5 ≤ a 5172 :=
  five_le_a_of_five_mem (n := 5172) (q1 := 59) (q2 := 151) (q3 := 179) (q4 := 241) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5178 : 5 ≤ a 5178 :=
  five_le_a_of_five_mem (n := 5178) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 101) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5184 : 5 ≤ a 5184 :=
  five_le_a_of_five_mem (n := 5184) (q1 := 5) (q2 := 13) (q3 := 97) (q4 := 163) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5190 : 5 ≤ a 5190 :=
  five_le_a_of_five_mem (n := 5190) (q1 := 19) (q2 := 37) (q3 := 43) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5196 : 5 ≤ a 5196 :=
  five_le_a_of_five_mem (n := 5196) (q1 := 83) (q2 := 137) (q3 := 197) (q4 := 223) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5202 : 5 ≤ a 5202 :=
  five_le_a_of_five_mem (n := 5202) (q1 := 31) (q2 := 101) (q3 := 179) (q4 := 191) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5208 : 5 ≤ a 5208 :=
  five_le_a_of_five_mem (n := 5208) (q1 := 19) (q2 := 29) (q3 := 89) (q4 := 101) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5214 : 5 ≤ a 5214 :=
  five_le_a_of_five_mem (n := 5214) (q1 := 17) (q2 := 47) (q3 := 67) (q4 := 137) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5220 : 5 ≤ a 5220 :=
  five_le_a_of_five_mem (n := 5220) (q1 := 11) (q2 := 41) (q3 := 53) (q4 := 113) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5226 : 5 ≤ a 5226 :=
  five_le_a_of_five_mem (n := 5226) (q1 := 47) (q2 := 107) (q3 := 167) (q4 := 223) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5232 : 5 ≤ a 5232 :=
  five_le_a_of_five_mem (n := 5232) (q1 := 5) (q2 := 181) (q3 := 211) (q4 := 239) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5238 : 5 ≤ a 5238 :=
  five_le_a_of_five_mem (n := 5238) (q1 := 41) (q2 := 59) (q3 := 71) (q4 := 179) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5244 : 5 ≤ a 5244 :=
  five_le_a_of_five_mem (n := 5244) (q1 := 17) (q2 := 137) (q3 := 163) (q4 := 193) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5250 : 5 ≤ a 5250 :=
  five_le_a_of_five_mem (n := 5250) (q1 := 23) (q2 := 53) (q3 := 83) (q4 := 97) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5256 : 5 ≤ a 5256 :=
  five_le_a_of_five_mem (n := 5256) (q1 := 23) (q2 := 47) (q3 := 67) (q4 := 137) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5262 : 5 ≤ a 5262 :=
  five_le_a_of_five_mem (n := 5262) (q1 := 181) (q2 := 239) (q3 := 241) (q4 := 269) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5268 : 5 ≤ a 5268 :=
  five_le_a_of_five_mem (n := 5268) (q1 := 41) (q2 := 79) (q3 := 149) (q4 := 181) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5274 : 5 ≤ a 5274 :=
  five_le_a_of_five_mem (n := 5274) (q1 := 107) (q2 := 167) (q3 := 197) (q4 := 307) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5280 : 5 ≤ a 5280 :=
  five_le_a_of_five_mem (n := 5280) (q1 := 43) (q2 := 53) (q3 := 71) (q4 := 101) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5286 : 5 ≤ a 5286 :=
  five_le_a_of_five_mem (n := 5286) (q1 := 107) (q2 := 277) (q3 := 283) (q4 := 353) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5292 : 5 ≤ a 5292 :=
  five_le_a_of_five_mem (n := 5292) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 139) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5298 : 5 ≤ a 5298 :=
  five_le_a_of_five_mem (n := 5298) (q1 := 89) (q2 := 101) (q3 := 109) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5304 : 5 ≤ a 5304 :=
  five_le_a_of_five_mem (n := 5304) (q1 := 43) (q2 := 137) (q3 := 197) (q4 := 223) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5310 : 5 ≤ a 5310 :=
  five_le_a_of_five_mem (n := 5310) (q1 := 13) (q2 := 37) (q3 := 83) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5316 : 5 ≤ a 5316 :=
  five_le_a_of_five_mem (n := 5316) (q1 := 7) (q2 := 83) (q3 := 127) (q4 := 163) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5322 : 5 ≤ a 5322 :=
  five_le_a_of_five_mem (n := 5322) (q1 := 241) (q2 := 379) (q3 := 389) (q4 := 419) (q5 := 461)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5328 : 5 ≤ a 5328 :=
  five_le_a_of_five_mem (n := 5328) (q1 := 5) (q2 := 19) (q3 := 149) (q4 := 229) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5334 : 5 ≤ a 5334 :=
  five_le_a_of_five_mem (n := 5334) (q1 := 53) (q2 := 73) (q3 := 97) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5340 : 5 ≤ a 5340 :=
  five_le_a_of_five_mem (n := 5340) (q1 := 7) (q2 := 59) (q3 := 67) (q4 := 79) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5346 : 5 ≤ a 5346 :=
  five_le_a_of_five_mem (n := 5346) (q1 := 67) (q2 := 73) (q3 := 137) (q4 := 157) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5352 : 5 ≤ a 5352 :=
  five_le_a_of_five_mem (n := 5352) (q1 := 29) (q2 := 79) (q3 := 239) (q4 := 271) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5358 : 5 ≤ a 5358 :=
  five_le_a_of_five_mem (n := 5358) (q1 := 61) (q2 := 79) (q3 := 149) (q4 := 211) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5364 : 5 ≤ a 5364 :=
  five_le_a_of_five_mem (n := 5364) (q1 := 17) (q2 := 67) (q3 := 137) (q4 := 167) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5370 : 5 ≤ a 5370 :=
  five_le_a_of_five_mem (n := 5370) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 61) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5376 : 5 ≤ a 5376 :=
  five_le_a_of_five_mem (n := 5376) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 103) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5382 : 5 ≤ a 5382 :=
  five_le_a_of_five_mem (n := 5382) (q1 := 31) (q2 := 59) (q3 := 101) (q4 := 149) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5388 : 5 ≤ a 5388 :=
  five_le_a_of_five_mem (n := 5388) (q1 := 269) (q2 := 281) (q3 := 349) (q4 := 419) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5394 : 5 ≤ a 5394 :=
  five_le_a_of_five_mem (n := 5394) (q1 := 13) (q2 := 43) (q3 := 47) (q4 := 113) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5400 : 5 ≤ a 5400 :=
  five_le_a_of_five_mem (n := 5400) (q1 := 7) (q2 := 13) (q3 := 19) (q4 := 103) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5406 : 5 ≤ a 5406 :=
  five_le_a_of_five_mem (n := 5406) (q1 := 7) (q2 := 13) (q3 := 73) (q4 := 97) (q5 := 433)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5412 : 5 ≤ a 5412 :=
  five_le_a_of_five_mem (n := 5412) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 89) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5418 : 5 ≤ a 5418 :=
  five_le_a_of_five_mem (n := 5418) (q1 := 19) (q2 := 31) (q3 := 109) (q4 := 139) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5424 : 5 ≤ a 5424 :=
  five_le_a_of_five_mem (n := 5424) (q1 := 7) (q2 := 17) (q3 := 227) (q4 := 277) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5430 : 5 ≤ a 5430 :=
  five_le_a_of_five_mem (n := 5430) (q1 := 11) (q2 := 13) (q3 := 97) (q4 := 127) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5436 : 5 ≤ a 5436 :=
  five_le_a_of_five_mem (n := 5436) (q1 := 5) (q2 := 43) (q3 := 127) (q4 := 257) (q5 := 433)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5442 : 5 ≤ a 5442 :=
  five_le_a_of_five_mem (n := 5442) (q1 := 29) (q2 := 61) (q3 := 139) (q4 := 181) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5448 : 5 ≤ a 5448 :=
  five_le_a_of_five_mem (n := 5448) (q1 := 29) (q2 := 31) (q3 := 211) (q4 := 269) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5454 : 5 ≤ a 5454 :=
  five_le_a_of_five_mem (n := 5454) (q1 := 17) (q2 := 23) (q3 := 47) (q4 := 67) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5460 : 5 ≤ a 5460 :=
  five_le_a_of_five_mem (n := 5460) (q1 := 11) (q2 := 17) (q3 := 19) (q4 := 23) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5466 : 5 ≤ a 5466 :=
  five_le_a_of_five_mem (n := 5466) (q1 := 17) (q2 := 53) (q3 := 157) (q4 := 193) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5472 : 5 ≤ a 5472 :=
  five_le_a_of_five_mem (n := 5472) (q1 := 29) (q2 := 31) (q3 := 59) (q4 := 211) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5478 : 5 ≤ a 5478 :=
  five_le_a_of_five_mem (n := 5478) (q1 := 29) (q2 := 41) (q3 := 79) (q4 := 181) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5484 : 5 ≤ a 5484 :=
  five_le_a_of_five_mem (n := 5484) (q1 := 43) (q2 := 47) (q3 := 97) (q4 := 257) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5490 : 5 ≤ a 5490 :=
  five_le_a_of_five_mem (n := 5490) (q1 := 11) (q2 := 13) (q3 := 41) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5496 : 5 ≤ a 5496 :=
  five_le_a_of_five_mem (n := 5496) (q1 := 163) (q2 := 173) (q3 := 193) (q4 := 317) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5502 : 5 ≤ a 5502 :=
  five_le_a_of_five_mem (n := 5502) (q1 := 19) (q2 := 61) (q3 := 71) (q4 := 89) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5508 : 5 ≤ a 5508 :=
  five_le_a_of_five_mem (n := 5508) (q1 := 229) (q2 := 271) (q3 := 389) (q4 := 431) (q5 := 499)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5514 : 5 ≤ a 5514 :=
  five_le_a_of_five_mem (n := 5514) (q1 := 7) (q2 := 13) (q3 := 43) (q4 := 127) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5520 : 5 ≤ a 5520 :=
  five_le_a_of_five_mem (n := 5520) (q1 := 37) (q2 := 43) (q3 := 71) (q4 := 103) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5526 : 5 ≤ a 5526 :=
  five_le_a_of_five_mem (n := 5526) (q1 := 5) (q2 := 43) (q3 := 47) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5532 : 5 ≤ a 5532 :=
  five_le_a_of_five_mem (n := 5532) (q1 := 31) (q2 := 151) (q3 := 251) (q4 := 521) (q5 := 599)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5538 : 5 ≤ a 5538 :=
  five_le_a_of_five_mem (n := 5538) (q1 := 19) (q2 := 31) (q3 := 101) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5544 : 5 ≤ a 5544 :=
  five_le_a_of_five_mem (n := 5544) (q1 := 13) (q2 := 37) (q3 := 103) (q4 := 107) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5550 : 5 ≤ a 5550 :=
  five_le_a_of_five_mem (n := 5550) (q1 := 19) (q2 := 23) (q3 := 31) (q4 := 73) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5556 : 5 ≤ a 5556 :=
  five_le_a_of_five_mem (n := 5556) (q1 := 113) (q2 := 137) (q3 := 223) (q4 := 283) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5562 : 5 ≤ a 5562 :=
  five_le_a_of_five_mem (n := 5562) (q1 := 61) (q2 := 79) (q3 := 131) (q4 := 149) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5568 : 5 ≤ a 5568 :=
  five_le_a_of_five_mem (n := 5568) (q1 := 5) (q2 := 89) (q3 := 149) (q4 := 181) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5574 : 5 ≤ a 5574 :=
  five_le_a_of_five_mem (n := 5574) (q1 := 17) (q2 := 67) (q3 := 73) (q4 := 137) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5580 : 5 ≤ a 5580 :=
  five_le_a_of_five_mem (n := 5580) (q1 := 11) (q2 := 59) (q3 := 61) (q4 := 73) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5586 : 5 ≤ a 5586 :=
  five_le_a_of_five_mem (n := 5586) (q1 := 5) (q2 := 67) (q3 := 83) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5592 : 5 ≤ a 5592 :=
  five_le_a_of_five_mem (n := 5592) (q1 := 61) (q2 := 109) (q3 := 149) (q4 := 151) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5598 : 5 ≤ a 5598 :=
  five_le_a_of_five_mem (n := 5598) (q1 := 41) (q2 := 71) (q3 := 181) (q4 := 251) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5604 : 5 ≤ a 5604 :=
  five_le_a_of_five_mem (n := 5604) (q1 := 47) (q2 := 97) (q3 := 197) (q4 := 223) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5610 : 5 ≤ a 5610 :=
  five_le_a_of_five_mem (n := 5610) (q1 := 29) (q2 := 37) (q3 := 41) (q4 := 47) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5616 : 5 ≤ a 5616 :=
  five_le_a_of_five_mem (n := 5616) (q1 := 43) (q2 := 53) (q3 := 167) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5622 : 5 ≤ a 5622 :=
  five_le_a_of_five_mem (n := 5622) (q1 := 31) (q2 := 179) (q3 := 191) (q4 := 229) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5628 : 5 ≤ a 5628 :=
  five_le_a_of_five_mem (n := 5628) (q1 := 109) (q2 := 151) (q3 := 179) (q4 := 211) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5634 : 5 ≤ a 5634 :=
  five_le_a_of_five_mem (n := 5634) (q1 := 103) (q2 := 107) (q3 := 157) (q4 := 193) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5640 : 5 ≤ a 5640 :=
  five_le_a_of_five_mem (n := 5640) (q1 := 17) (q2 := 71) (q3 := 109) (q4 := 139) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5646 : 5 ≤ a 5646 :=
  five_le_a_of_five_mem (n := 5646) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 167) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5652 : 5 ≤ a 5652 :=
  five_le_a_of_five_mem (n := 5652) (q1 := 5) (q2 := 89) (q3 := 131) (q4 := 149) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5658 : 5 ≤ a 5658 :=
  five_le_a_of_five_mem (n := 5658) (q1 := 11) (q2 := 181) (q3 := 239) (q4 := 349) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5664 : 5 ≤ a 5664 :=
  five_le_a_of_five_mem (n := 5664) (q1 := 5) (q2 := 73) (q3 := 137) (q4 := 157) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5670 : 5 ≤ a 5670 :=
  five_le_a_of_five_mem (n := 5670) (q1 := 13) (q2 := 19) (q3 := 23) (q4 := 31) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5676 : 5 ≤ a 5676 :=
  five_le_a_of_five_mem (n := 5676) (q1 := 7) (q2 := 17) (q3 := 103) (q4 := 107) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5682 : 5 ≤ a 5682 :=
  five_le_a_of_five_mem (n := 5682) (q1 := 29) (q2 := 59) (q3 := 101) (q4 := 109) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5688 : 5 ≤ a 5688 :=
  five_le_a_of_five_mem (n := 5688) (q1 := 5) (q2 := 29) (q3 := 181) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5694 : 5 ≤ a 5694 :=
  five_le_a_of_five_mem (n := 5694) (q1 := 43) (q2 := 47) (q3 := 113) (q4 := 163) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5700 : 5 ≤ a 5700 :=
  five_le_a_of_five_mem (n := 5700) (q1 := 11) (q2 := 17) (q3 := 41) (q4 := 43) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5706 : 5 ≤ a 5706 :=
  five_le_a_of_five_mem (n := 5706) (q1 := 5) (q2 := 37) (q3 := 137) (q4 := 373) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5712 : 5 ≤ a 5712 :=
  five_le_a_of_five_mem (n := 5712) (q1 := 29) (q2 := 71) (q3 := 89) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5718 : 5 ≤ a 5718 :=
  five_le_a_of_five_mem (n := 5718) (q1 := 61) (q2 := 149) (q3 := 269) (q4 := 311) (q5 := 599)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5724 : 5 ≤ a 5724 :=
  five_le_a_of_five_mem (n := 5724) (q1 := 13) (q2 := 67) (q3 := 83) (q4 := 283) (q5 := 487)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5730 : 5 ≤ a 5730 :=
  five_le_a_of_five_mem (n := 5730) (q1 := 13) (q2 := 19) (q3 := 61) (q4 := 71) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5736 : 5 ≤ a 5736 :=
  five_le_a_of_five_mem (n := 5736) (q1 := 43) (q2 := 47) (q3 := 113) (q4 := 167) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5742 : 5 ≤ a 5742 :=
  five_le_a_of_five_mem (n := 5742) (q1 := 41) (q2 := 59) (q3 := 101) (q4 := 211) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5748 : 5 ≤ a 5748 :=
  five_le_a_of_five_mem (n := 5748) (q1 := 31) (q2 := 59) (q3 := 79) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5754 : 5 ≤ a 5754 :=
  five_le_a_of_five_mem (n := 5754) (q1 := 37) (q2 := 53) (q3 := 97) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5760 : 5 ≤ a 5760 :=
  five_le_a_of_five_mem (n := 5760) (q1 := 19) (q2 := 23) (q3 := 67) (q4 := 101) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5766 : 5 ≤ a 5766 :=
  five_le_a_of_five_mem (n := 5766) (q1 := 17) (q2 := 73) (q3 := 83) (q4 := 113) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5772 : 5 ≤ a 5772 :=
  five_le_a_of_five_mem (n := 5772) (q1 := 29) (q2 := 71) (q3 := 79) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5778 : 5 ≤ a 5778 :=
  five_le_a_of_five_mem (n := 5778) (q1 := 29) (q2 := 61) (q3 := 89) (q4 := 251) (q5 := 499)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5784 : 5 ≤ a 5784 :=
  five_le_a_of_five_mem (n := 5784) (q1 := 43) (q2 := 67) (q3 := 73) (q4 := 83) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5790 : 5 ≤ a 5790 :=
  five_le_a_of_five_mem (n := 5790) (q1 := 11) (q2 := 53) (q3 := 79) (q4 := 89) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5796 : 5 ≤ a 5796 :=
  five_le_a_of_five_mem (n := 5796) (q1 := 5) (q2 := 17) (q3 := 47) (q4 := 53) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5802 : 5 ≤ a 5802 :=
  five_le_a_of_five_mem (n := 5802) (q1 := 11) (q2 := 19) (q3 := 59) (q4 := 101) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5808 : 5 ≤ a 5808 :=
  five_le_a_of_five_mem (n := 5808) (q1 := 59) (q2 := 71) (q3 := 239) (q4 := 281) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5814 : 5 ≤ a 5814 :=
  five_le_a_of_five_mem (n := 5814) (q1 := 7) (q2 := 13) (q3 := 113) (q4 := 167) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5820 : 5 ≤ a 5820 :=
  five_le_a_of_five_mem (n := 5820) (q1 := 7) (q2 := 19) (q3 := 29) (q4 := 37) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5826 : 5 ≤ a 5826 :=
  five_le_a_of_five_mem (n := 5826) (q1 := 13) (q2 := 43) (q3 := 263) (q4 := 307) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5832 : 5 ≤ a 5832 :=
  five_le_a_of_five_mem (n := 5832) (q1 := 11) (q2 := 19) (q3 := 149) (q4 := 179) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5838 : 5 ≤ a 5838 :=
  five_le_a_of_five_mem (n := 5838) (q1 := 11) (q2 := 31) (q3 := 59) (q4 := 89) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5844 : 5 ≤ a 5844 :=
  five_le_a_of_five_mem (n := 5844) (q1 := 5) (q2 := 17) (q3 := 23) (q4 := 37) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5850 : 5 ≤ a 5850 :=
  five_le_a_of_five_mem (n := 5850) (q1 := 7) (q2 := 11) (q3 := 29) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5856 : 5 ≤ a 5856 :=
  five_le_a_of_five_mem (n := 5856) (q1 := 5) (q2 := 13) (q3 := 173) (q4 := 197) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5862 : 5 ≤ a 5862 :=
  five_le_a_of_five_mem (n := 5862) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 61) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5868 : 5 ≤ a 5868 :=
  five_le_a_of_five_mem (n := 5868) (q1 := 11) (q2 := 29) (q3 := 179) (q4 := 199) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5874 : 5 ≤ a 5874 :=
  five_le_a_of_five_mem (n := 5874) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 53) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5880 : 5 ≤ a 5880 :=
  five_le_a_of_five_mem (n := 5880) (q1 := 23) (q2 := 59) (q3 := 73) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5886 : 5 ≤ a 5886 :=
  five_le_a_of_five_mem (n := 5886) (q1 := 17) (q2 := 37) (q3 := 193) (q4 := 227) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5892 : 5 ≤ a 5892 :=
  five_le_a_of_five_mem (n := 5892) (q1 := 11) (q2 := 31) (q3 := 151) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5898 : 5 ≤ a 5898 :=
  five_le_a_of_five_mem (n := 5898) (q1 := 29) (q2 := 41) (q3 := 149) (q4 := 181) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5904 : 5 ≤ a 5904 :=
  five_le_a_of_five_mem (n := 5904) (q1 := 23) (q2 := 83) (q3 := 103) (q4 := 163) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5910 : 5 ≤ a 5910 :=
  five_le_a_of_five_mem (n := 5910) (q1 := 13) (q2 := 29) (q3 := 43) (q4 := 71) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5916 : 5 ≤ a 5916 :=
  five_le_a_of_five_mem (n := 5916) (q1 := 37) (q2 := 137) (q3 := 173) (q4 := 227) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5922 : 5 ≤ a 5922 :=
  five_le_a_of_five_mem (n := 5922) (q1 := 131) (q2 := 179) (q3 := 211) (q4 := 229) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5928 : 5 ≤ a 5928 :=
  five_le_a_of_five_mem (n := 5928) (q1 := 59) (q2 := 79) (q3 := 101) (q4 := 269) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5934 : 5 ≤ a 5934 :=
  five_le_a_of_five_mem (n := 5934) (q1 := 53) (q2 := 73) (q3 := 113) (q4 := 197) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5940 : 5 ≤ a 5940 :=
  five_le_a_of_five_mem (n := 5940) (q1 := 13) (q2 := 71) (q3 := 89) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5946 : 5 ≤ a 5946 :=
  five_le_a_of_five_mem (n := 5946) (q1 := 7) (q2 := 97) (q3 := 107) (q4 := 167) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5952 : 5 ≤ a 5952 :=
  five_le_a_of_five_mem (n := 5952) (q1 := 29) (q2 := 101) (q3 := 139) (q4 := 211) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5958 : 5 ≤ a 5958 :=
  five_le_a_of_five_mem (n := 5958) (q1 := 79) (q2 := 89) (q3 := 109) (q4 := 131) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5964 : 5 ≤ a 5964 :=
  five_le_a_of_five_mem (n := 5964) (q1 := 83) (q2 := 103) (q3 := 137) (q4 := 157) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5970 : 5 ≤ a 5970 :=
  five_le_a_of_five_mem (n := 5970) (q1 := 17) (q2 := 67) (q3 := 73) (q4 := 103) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5976 : 5 ≤ a 5976 :=
  five_le_a_of_five_mem (n := 5976) (q1 := 53) (q2 := 97) (q3 := 137) (q4 := 197) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5982 : 5 ≤ a 5982 :=
  five_le_a_of_five_mem (n := 5982) (q1 := 29) (q2 := 131) (q3 := 139) (q4 := 181) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5988 : 5 ≤ a 5988 :=
  five_le_a_of_five_mem (n := 5988) (q1 := 349) (q2 := 461) (q3 := 691) (q4 := 881) (q5 := 911)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_5994 : 5 ≤ a 5994 :=
  five_le_a_of_five_mem (n := 5994) (q1 := 13) (q2 := 97) (q3 := 127) (q4 := 137) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6000 : 5 ≤ a 6000 :=
  five_le_a_of_five_mem (n := 6000) (q1 := 47) (q2 := 73) (q3 := 131) (q4 := 151) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6006 : 5 ≤ a 6006 :=
  five_le_a_of_five_mem (n := 6006) (q1 := 67) (q2 := 83) (q3 := 127) (q4 := 137) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6012 : 5 ≤ a 6012 :=
  five_le_a_of_five_mem (n := 6012) (q1 := 31) (q2 := 89) (q3 := 109) (q4 := 131) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6018 : 5 ≤ a 6018 :=
  five_le_a_of_five_mem (n := 6018) (q1 := 11) (q2 := 179) (q3 := 211) (q4 := 239) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6024 : 5 ≤ a 6024 :=
  five_le_a_of_five_mem (n := 6024) (q1 := 13) (q2 := 43) (q3 := 97) (q4 := 127) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6030 : 5 ≤ a 6030 :=
  five_le_a_of_five_mem (n := 6030) (q1 := 23) (q2 := 43) (q3 := 103) (q4 := 173) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6036 : 5 ≤ a 6036 :=
  five_le_a_of_five_mem (n := 6036) (q1 := 7) (q2 := 97) (q3 := 167) (q4 := 193) (q5 := 293)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6042 : 5 ≤ a 6042 :=
  five_le_a_of_five_mem (n := 6042) (q1 := 5) (q2 := 31) (q3 := 89) (q4 := 229) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6048 : 5 ≤ a 6048 :=
  five_le_a_of_five_mem (n := 6048) (q1 := 5) (q2 := 19) (q3 := 41) (q4 := 151) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6054 : 5 ≤ a 6054 :=
  five_le_a_of_five_mem (n := 6054) (q1 := 47) (q2 := 67) (q3 := 157) (q4 := 193) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6060 : 5 ≤ a 6060 :=
  five_le_a_of_five_mem (n := 6060) (q1 := 7) (q2 := 13) (q3 := 31) (q4 := 53) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6066 : 5 ≤ a 6066 :=
  five_le_a_of_five_mem (n := 6066) (q1 := 13) (q2 := 23) (q3 := 163) (q4 := 197) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6072 : 5 ≤ a 6072 :=
  five_le_a_of_five_mem (n := 6072) (q1 := 19) (q2 := 29) (q3 := 61) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6078 : 5 ≤ a 6078 :=
  five_le_a_of_five_mem (n := 6078) (q1 := 11) (q2 := 139) (q3 := 151) (q4 := 199) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6084 : 5 ≤ a 6084 :=
  five_le_a_of_five_mem (n := 6084) (q1 := 5) (q2 := 17) (q3 := 37) (q4 := 47) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6090 : 5 ≤ a 6090 :=
  five_le_a_of_five_mem (n := 6090) (q1 := 11) (q2 := 23) (q3 := 43) (q4 := 53) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6096 : 5 ≤ a 6096 :=
  five_le_a_of_five_mem (n := 6096) (q1 := 5) (q2 := 17) (q3 := 67) (q4 := 173) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6102 : 5 ≤ a 6102 :=
  five_le_a_of_five_mem (n := 6102) (q1 := 11) (q2 := 29) (q3 := 199) (q4 := 241) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6108 : 5 ≤ a 6108 :=
  five_le_a_of_five_mem (n := 6108) (q1 := 229) (q2 := 251) (q3 := 281) (q4 := 439) (q5 := 461)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6114 : 5 ≤ a 6114 :=
  five_le_a_of_five_mem (n := 6114) (q1 := 103) (q2 := 107) (q3 := 307) (q4 := 313) (q5 := 457)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6120 : 5 ≤ a 6120 :=
  five_le_a_of_five_mem (n := 6120) (q1 := 31) (q2 := 53) (q3 := 83) (q4 := 109) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6126 : 5 ≤ a 6126 :=
  five_le_a_of_five_mem (n := 6126) (q1 := 5) (q2 := 37) (q3 := 47) (q4 := 73) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6132 : 5 ≤ a 6132 :=
  five_le_a_of_five_mem (n := 6132) (q1 := 11) (q2 := 19) (q3 := 31) (q4 := 41) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6138 : 5 ≤ a 6138 :=
  five_le_a_of_five_mem (n := 6138) (q1 := 5) (q2 := 59) (q3 := 109) (q4 := 131) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6144 : 5 ≤ a 6144 :=
  five_le_a_of_five_mem (n := 6144) (q1 := 53) (q2 := 157) (q3 := 277) (q4 := 283) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6150 : 5 ≤ a 6150 :=
  five_le_a_of_five_mem (n := 6150) (q1 := 61) (q2 := 71) (q3 := 97) (q4 := 107) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6156 : 5 ≤ a 6156 :=
  five_le_a_of_five_mem (n := 6156) (q1 := 43) (q2 := 113) (q3 := 233) (q4 := 313) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6162 : 5 ≤ a 6162 :=
  five_le_a_of_five_mem (n := 6162) (q1 := 11) (q2 := 41) (q3 := 109) (q4 := 181) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6168 : 5 ≤ a 6168 :=
  five_le_a_of_five_mem (n := 6168) (q1 := 5) (q2 := 79) (q3 := 89) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6174 : 5 ≤ a 6174 :=
  five_le_a_of_five_mem (n := 6174) (q1 := 23) (q2 := 43) (q3 := 73) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6180 : 5 ≤ a 6180 :=
  five_le_a_of_five_mem (n := 6180) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 89) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6186 : 5 ≤ a 6186 :=
  five_le_a_of_five_mem (n := 6186) (q1 := 13) (q2 := 43) (q3 := 113) (q4 := 157) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6192 : 5 ≤ a 6192 :=
  five_le_a_of_five_mem (n := 6192) (q1 := 19) (q2 := 29) (q3 := 71) (q4 := 79) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6198 : 5 ≤ a 6198 :=
  five_le_a_of_five_mem (n := 6198) (q1 := 131) (q2 := 191) (q3 := 271) (q4 := 331) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6204 : 5 ≤ a 6204 :=
  five_le_a_of_five_mem (n := 6204) (q1 := 7) (q2 := 53) (q3 := 73) (q4 := 83) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6210 : 5 ≤ a 6210 :=
  five_le_a_of_five_mem (n := 6210) (q1 := 7) (q2 := 11) (q3 := 37) (q4 := 47) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6216 : 5 ≤ a 6216 :=
  five_le_a_of_five_mem (n := 6216) (q1 := 5) (q2 := 13) (q3 := 53) (q4 := 83) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6222 : 5 ≤ a 6222 :=
  five_le_a_of_five_mem (n := 6222) (q1 := 79) (q2 := 89) (q3 := 101) (q4 := 131) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6228 : 5 ≤ a 6228 :=
  five_le_a_of_five_mem (n := 6228) (q1 := 29) (q2 := 139) (q3 := 199) (q4 := 241) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6234 : 5 ≤ a 6234 :=
  five_le_a_of_five_mem (n := 6234) (q1 := 13) (q2 := 23) (q3 := 37) (q4 := 83) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6240 : 5 ≤ a 6240 :=
  five_le_a_of_five_mem (n := 6240) (q1 := 23) (q2 := 29) (q3 := 37) (q4 := 89) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6246 : 5 ≤ a 6246 :=
  five_le_a_of_five_mem (n := 6246) (q1 := 17) (q2 := 83) (q3 := 113) (q4 := 307) (q5 := 433)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6252 : 5 ≤ a 6252 :=
  five_le_a_of_five_mem (n := 6252) (q1 := 5) (q2 := 101) (q3 := 109) (q4 := 199) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6258 : 5 ≤ a 6258 :=
  five_le_a_of_five_mem (n := 6258) (q1 := 11) (q2 := 29) (q3 := 41) (q4 := 59) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6264 : 5 ≤ a 6264 :=
  five_le_a_of_five_mem (n := 6264) (q1 := 7) (q2 := 47) (q3 := 53) (q4 := 163) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6270 : 5 ≤ a 6270 :=
  five_le_a_of_five_mem (n := 6270) (q1 := 7) (q2 := 41) (q3 := 53) (q4 := 59) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6276 : 5 ≤ a 6276 :=
  five_le_a_of_five_mem (n := 6276) (q1 := 47) (q2 := 103) (q3 := 113) (q4 := 197) (q5 := 397)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6282 : 5 ≤ a 6282 :=
  five_le_a_of_five_mem (n := 6282) (q1 := 5) (q2 := 19) (q3 := 61) (q4 := 71) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6288 : 5 ≤ a 6288 :=
  five_le_a_of_five_mem (n := 6288) (q1 := 11) (q2 := 41) (q3 := 71) (q4 := 241) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6294 : 5 ≤ a 6294 :=
  five_le_a_of_five_mem (n := 6294) (q1 := 7) (q2 := 17) (q3 := 23) (q4 := 73) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6300 : 5 ≤ a 6300 :=
  five_le_a_of_five_mem (n := 6300) (q1 := 23) (q2 := 29) (q3 := 37) (q4 := 43) (q5 := 53)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6306 : 5 ≤ a 6306 :=
  five_le_a_of_five_mem (n := 6306) (q1 := 5) (q2 := 37) (q3 := 163) (q4 := 263) (q5 := 353)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6312 : 5 ≤ a 6312 :=
  five_le_a_of_five_mem (n := 6312) (q1 := 11) (q2 := 41) (q3 := 109) (q4 := 139) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6318 : 5 ≤ a 6318 :=
  five_le_a_of_five_mem (n := 6318) (q1 := 19) (q2 := 41) (q3 := 61) (q4 := 71) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6324 : 5 ≤ a 6324 :=
  five_le_a_of_five_mem (n := 6324) (q1 := 13) (q2 := 37) (q3 := 103) (q4 := 127) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6330 : 5 ≤ a 6330 :=
  five_le_a_of_five_mem (n := 6330) (q1 := 7) (q2 := 13) (q3 := 29) (q4 := 31) (q5 := 43)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6336 : 5 ≤ a 6336 :=
  five_le_a_of_five_mem (n := 6336) (q1 := 7) (q2 := 37) (q3 := 137) (q4 := 193) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6342 : 5 ≤ a 6342 :=
  five_le_a_of_five_mem (n := 6342) (q1 := 19) (q2 := 31) (q3 := 79) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6348 : 5 ≤ a 6348 :=
  five_le_a_of_five_mem (n := 6348) (q1 := 5) (q2 := 11) (q3 := 19) (q4 := 31) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6354 : 5 ≤ a 6354 :=
  five_le_a_of_five_mem (n := 6354) (q1 := 43) (q2 := 67) (q3 := 97) (q4 := 137) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6360 : 5 ≤ a 6360 :=
  five_le_a_of_five_mem (n := 6360) (q1 := 7) (q2 := 37) (q3 := 61) (q4 := 89) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6366 : 5 ≤ a 6366 :=
  five_le_a_of_five_mem (n := 6366) (q1 := 7) (q2 := 13) (q3 := 23) (q4 := 103) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6372 : 5 ≤ a 6372 :=
  five_le_a_of_five_mem (n := 6372) (q1 := 101) (q2 := 109) (q3 := 199) (q4 := 281) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6378 : 5 ≤ a 6378 :=
  five_le_a_of_five_mem (n := 6378) (q1 := 11) (q2 := 19) (q3 := 311) (q4 := 331) (q5 := 521)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6384 : 5 ≤ a 6384 :=
  five_le_a_of_five_mem (n := 6384) (q1 := 5) (q2 := 67) (q3 := 97) (q4 := 107) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6390 : 5 ≤ a 6390 :=
  five_le_a_of_five_mem (n := 6390) (q1 := 31) (q2 := 37) (q3 := 61) (q4 := 79) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6396 : 5 ≤ a 6396 :=
  five_le_a_of_five_mem (n := 6396) (q1 := 53) (q2 := 73) (q3 := 167) (q4 := 223) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6402 : 5 ≤ a 6402 :=
  five_le_a_of_five_mem (n := 6402) (q1 := 79) (q2 := 251) (q3 := 271) (q4 := 359) (q5 := 421)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6408 : 5 ≤ a 6408 :=
  five_le_a_of_five_mem (n := 6408) (q1 := 19) (q2 := 41) (q3 := 139) (q4 := 191) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6414 : 5 ≤ a 6414 :=
  five_le_a_of_five_mem (n := 6414) (q1 := 137) (q2 := 157) (q3 := 167) (q4 := 193) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6420 : 5 ≤ a 6420 :=
  five_le_a_of_five_mem (n := 6420) (q1 := 31) (q2 := 53) (q3 := 61) (q4 := 109) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6426 : 5 ≤ a 6426 :=
  five_le_a_of_five_mem (n := 6426) (q1 := 47) (q2 := 103) (q3 := 127) (q4 := 227) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6432 : 5 ≤ a 6432 :=
  five_le_a_of_five_mem (n := 6432) (q1 := 59) (q2 := 89) (q3 := 131) (q4 := 229) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6438 : 5 ≤ a 6438 :=
  five_le_a_of_five_mem (n := 6438) (q1 := 11) (q2 := 109) (q3 := 139) (q4 := 181) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6444 : 5 ≤ a 6444 :=
  five_le_a_of_five_mem (n := 6444) (q1 := 47) (q2 := 107) (q3 := 127) (q4 := 293) (q5 := 397)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6450 : 5 ≤ a 6450 :=
  five_le_a_of_five_mem (n := 6450) (q1 := 23) (q2 := 71) (q3 := 97) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6456 : 5 ≤ a 6456 :=
  five_le_a_of_five_mem (n := 6456) (q1 := 97) (q2 := 113) (q3 := 367) (q4 := 503) (q5 := 587)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6462 : 5 ≤ a 6462 :=
  five_le_a_of_five_mem (n := 6462) (q1 := 11) (q2 := 89) (q3 := 101) (q4 := 109) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6468 : 5 ≤ a 6468 :=
  five_le_a_of_five_mem (n := 6468) (q1 := 79) (q2 := 101) (q3 := 109) (q4 := 131) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6474 : 5 ≤ a 6474 :=
  five_le_a_of_five_mem (n := 6474) (q1 := 47) (q2 := 107) (q3 := 163) (q4 := 227) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6480 : 5 ≤ a 6480 :=
  five_le_a_of_five_mem (n := 6480) (q1 := 11) (q2 := 83) (q3 := 101) (q4 := 127) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6486 : 5 ≤ a 6486 :=
  five_le_a_of_five_mem (n := 6486) (q1 := 5) (q2 := 113) (q3 := 223) (q4 := 397) (q5 := 617)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6492 : 5 ≤ a 6492 :=
  five_le_a_of_five_mem (n := 6492) (q1 := 71) (q2 := 181) (q3 := 271) (q4 := 349) (q5 := 379)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6498 : 5 ≤ a 6498 :=
  five_le_a_of_five_mem (n := 6498) (q1 := 71) (q2 := 101) (q3 := 109) (q4 := 139) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6504 : 5 ≤ a 6504 :=
  five_le_a_of_five_mem (n := 6504) (q1 := 233) (q2 := 257) (q3 := 353) (q4 := 457) (q5 := 467)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6510 : 5 ≤ a 6510 :=
  five_le_a_of_five_mem (n := 6510) (q1 := 19) (q2 := 37) (q3 := 41) (q4 := 59) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6516 : 5 ≤ a 6516 :=
  five_le_a_of_five_mem (n := 6516) (q1 := 47) (q2 := 137) (q3 := 157) (q4 := 163) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6522 : 5 ≤ a 6522 :=
  five_le_a_of_five_mem (n := 6522) (q1 := 31) (q2 := 41) (q3 := 179) (q4 := 211) (q5 := 311)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6528 : 5 ≤ a 6528 :=
  five_le_a_of_five_mem (n := 6528) (q1 := 79) (q2 := 131) (q3 := 191) (q4 := 251) (q5 := 439)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6534 : 5 ≤ a 6534 :=
  five_le_a_of_five_mem (n := 6534) (q1 := 13) (q2 := 43) (q3 := 167) (q4 := 257) (q5 := 337)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6540 : 5 ≤ a 6540 :=
  five_le_a_of_five_mem (n := 6540) (q1 := 11) (q2 := 59) (q3 := 67) (q4 := 113) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6546 : 5 ≤ a 6546 :=
  five_le_a_of_five_mem (n := 6546) (q1 := 17) (q2 := 73) (q3 := 157) (q4 := 173) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6552 : 5 ≤ a 6552 :=
  five_le_a_of_five_mem (n := 6552) (q1 := 101) (q2 := 229) (q3 := 241) (q4 := 251) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6558 : 5 ≤ a 6558 :=
  five_le_a_of_five_mem (n := 6558) (q1 := 5) (q2 := 11) (q3 := 131) (q4 := 179) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6564 : 5 ≤ a 6564 :=
  five_le_a_of_five_mem (n := 6564) (q1 := 13) (q2 := 17) (q3 := 43) (q4 := 73) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6570 : 5 ≤ a 6570 :=
  five_le_a_of_five_mem (n := 6570) (q1 := 7) (q2 := 89) (q3 := 149) (q4 := 191) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6576 : 5 ≤ a 6576 :=
  five_le_a_of_five_mem (n := 6576) (q1 := 5) (q2 := 23) (q3 := 103) (q4 := 127) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6582 : 5 ≤ a 6582 :=
  five_le_a_of_five_mem (n := 6582) (q1 := 109) (q2 := 281) (q3 := 379) (q4 := 409) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6588 : 5 ≤ a 6588 :=
  five_le_a_of_five_mem (n := 6588) (q1 := 11) (q2 := 19) (q3 := 191) (q4 := 311) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6594 : 5 ≤ a 6594 :=
  five_le_a_of_five_mem (n := 6594) (q1 := 13) (q2 := 43) (q3 := 167) (q4 := 197) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6600 : 5 ≤ a 6600 :=
  five_le_a_of_five_mem (n := 6600) (q1 := 19) (q2 := 37) (q3 := 53) (q4 := 79) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6606 : 5 ≤ a 6606 :=
  five_le_a_of_five_mem (n := 6606) (q1 := 53) (q2 := 157) (q3 := 227) (q4 := 263) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6612 : 5 ≤ a 6612 :=
  five_le_a_of_five_mem (n := 6612) (q1 := 41) (q2 := 61) (q3 := 191) (q4 := 251) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6618 : 5 ≤ a 6618 :=
  five_le_a_of_five_mem (n := 6618) (q1 := 19) (q2 := 41) (q3 := 71) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6624 : 5 ≤ a 6624 :=
  five_le_a_of_five_mem (n := 6624) (q1 := 337) (q2 := 347) (q3 := 353) (q4 := 367) (q5 := 503)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6630 : 5 ≤ a 6630 :=
  five_le_a_of_five_mem (n := 6630) (q1 := 23) (q2 := 31) (q3 := 59) (q4 := 61) (q5 := 79)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6636 : 5 ≤ a 6636 :=
  five_le_a_of_five_mem (n := 6636) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 73) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6642 : 5 ≤ a 6642 :=
  five_le_a_of_five_mem (n := 6642) (q1 := 61) (q2 := 151) (q3 := 191) (q4 := 269) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6648 : 5 ≤ a 6648 :=
  five_le_a_of_five_mem (n := 6648) (q1 := 11) (q2 := 41) (q3 := 71) (q4 := 179) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6654 : 5 ≤ a 6654 :=
  five_le_a_of_five_mem (n := 6654) (q1 := 47) (q2 := 83) (q3 := 107) (q4 := 173) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6660 : 5 ≤ a 6660 :=
  five_le_a_of_five_mem (n := 6660) (q1 := 41) (q2 := 131) (q3 := 211) (q4 := 239) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6666 : 5 ≤ a 6666 :=
  five_le_a_of_five_mem (n := 6666) (q1 := 7) (q2 := 13) (q3 := 67) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6672 : 5 ≤ a 6672 :=
  five_le_a_of_five_mem (n := 6672) (q1 := 19) (q2 := 109) (q3 := 151) (q4 := 191) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6678 : 5 ≤ a 6678 :=
  five_le_a_of_five_mem (n := 6678) (q1 := 41) (q2 := 59) (q3 := 101) (q4 := 149) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6684 : 5 ≤ a 6684 :=
  five_le_a_of_five_mem (n := 6684) (q1 := 5) (q2 := 107) (q3 := 233) (q4 := 263) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6690 : 5 ≤ a 6690 :=
  five_le_a_of_five_mem (n := 6690) (q1 := 11) (q2 := 29) (q3 := 71) (q4 := 113) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6696 : 5 ≤ a 6696 :=
  five_le_a_of_five_mem (n := 6696) (q1 := 5) (q2 := 7) (q3 := 23) (q4 := 37) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6702 : 5 ≤ a 6702 :=
  five_le_a_of_five_mem (n := 6702) (q1 := 131) (q2 := 139) (q3 := 181) (q4 := 281) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6708 : 5 ≤ a 6708 :=
  five_le_a_of_five_mem (n := 6708) (q1 := 29) (q2 := 71) (q3 := 239) (q4 := 311) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6714 : 5 ≤ a 6714 :=
  five_le_a_of_five_mem (n := 6714) (q1 := 5) (q2 := 23) (q3 := 193) (q4 := 233) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6720 : 5 ≤ a 6720 :=
  five_le_a_of_five_mem (n := 6720) (q1 := 17) (q2 := 41) (q3 := 59) (q4 := 61) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6726 : 5 ≤ a 6726 :=
  five_le_a_of_five_mem (n := 6726) (q1 := 7) (q2 := 37) (q3 := 53) (q4 := 67) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6732 : 5 ≤ a 6732 :=
  five_le_a_of_five_mem (n := 6732) (q1 := 29) (q2 := 31) (q3 := 59) (q4 := 71) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6738 : 5 ≤ a 6738 :=
  five_le_a_of_five_mem (n := 6738) (q1 := 131) (q2 := 421) (q3 := 439) (q4 := 491) (q5 := 509)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6744 : 5 ≤ a 6744 :=
  five_le_a_of_five_mem (n := 6744) (q1 := 83) (q2 := 163) (q3 := 167) (q4 := 173) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6750 : 5 ≤ a 6750 :=
  five_le_a_of_five_mem (n := 6750) (q1 := 13) (q2 := 31) (q3 := 41) (q4 := 113) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6756 : 5 ≤ a 6756 :=
  five_le_a_of_five_mem (n := 6756) (q1 := 23) (q2 := 37) (q3 := 47) (q4 := 67) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6762 : 5 ≤ a 6762 :=
  five_le_a_of_five_mem (n := 6762) (q1 := 29) (q2 := 61) (q3 := 71) (q4 := 101) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6768 : 5 ≤ a 6768 :=
  five_le_a_of_five_mem (n := 6768) (q1 := 59) (q2 := 89) (q3 := 131) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6774 : 5 ≤ a 6774 :=
  five_le_a_of_five_mem (n := 6774) (q1 := 83) (q2 := 137) (q3 := 193) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6780 : 5 ≤ a 6780 :=
  five_le_a_of_five_mem (n := 6780) (q1 := 43) (q2 := 47) (q3 := 61) (q4 := 89) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6786 : 5 ≤ a 6786 :=
  five_le_a_of_five_mem (n := 6786) (q1 := 5) (q2 := 7) (q3 := 83) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6792 : 5 ≤ a 6792 :=
  five_le_a_of_five_mem (n := 6792) (q1 := 11) (q2 := 31) (q3 := 311) (q4 := 419) (q5 := 491)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6798 : 5 ≤ a 6798 :=
  five_le_a_of_five_mem (n := 6798) (q1 := 5) (q2 := 109) (q3 := 179) (q4 := 199) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6804 : 5 ≤ a 6804 :=
  five_le_a_of_five_mem (n := 6804) (q1 := 23) (q2 := 67) (q3 := 103) (q4 := 113) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6810 : 5 ≤ a 6810 :=
  five_le_a_of_five_mem (n := 6810) (q1 := 17) (q2 := 19) (q3 := 31) (q4 := 47) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6816 : 5 ≤ a 6816 :=
  five_le_a_of_five_mem (n := 6816) (q1 := 13) (q2 := 53) (q3 := 83) (q4 := 197) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6822 : 5 ≤ a 6822 :=
  five_le_a_of_five_mem (n := 6822) (q1 := 19) (q2 := 41) (q3 := 61) (q4 := 89) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6828 : 5 ≤ a 6828 :=
  five_le_a_of_five_mem (n := 6828) (q1 := 5) (q2 := 139) (q3 := 149) (q4 := 191) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6834 : 5 ≤ a 6834 :=
  five_le_a_of_five_mem (n := 6834) (q1 := 7) (q2 := 73) (q3 := 353) (q4 := 577) (q5 := 617)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6840 : 5 ≤ a 6840 :=
  five_le_a_of_five_mem (n := 6840) (q1 := 17) (q2 := 59) (q3 := 107) (q4 := 131) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6846 : 5 ≤ a 6846 :=
  five_le_a_of_five_mem (n := 6846) (q1 := 17) (q2 := 23) (q3 := 53) (q4 := 113) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6852 : 5 ≤ a 6852 :=
  five_le_a_of_five_mem (n := 6852) (q1 := 11) (q2 := 19) (q3 := 59) (q4 := 149) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6858 : 5 ≤ a 6858 :=
  five_le_a_of_five_mem (n := 6858) (q1 := 139) (q2 := 199) (q3 := 251) (q4 := 389) (q5 := 491)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6864 : 5 ≤ a 6864 :=
  five_le_a_of_five_mem (n := 6864) (q1 := 7) (q2 := 83) (q3 := 103) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6870 : 5 ≤ a 6870 :=
  five_le_a_of_five_mem (n := 6870) (q1 := 13) (q2 := 29) (q3 := 37) (q4 := 41) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6876 : 5 ≤ a 6876 :=
  five_le_a_of_five_mem (n := 6876) (q1 := 7) (q2 := 73) (q3 := 83) (q4 := 167) (q5 := 613)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6882 : 5 ≤ a 6882 :=
  five_le_a_of_five_mem (n := 6882) (q1 := 79) (q2 := 89) (q3 := 101) (q4 := 311) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6888 : 5 ≤ a 6888 :=
  five_le_a_of_five_mem (n := 6888) (q1 := 19) (q2 := 59) (q3 := 61) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6894 : 5 ≤ a 6894 :=
  five_le_a_of_five_mem (n := 6894) (q1 := 23) (q2 := 53) (q3 := 67) (q4 := 103) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6900 : 5 ≤ a 6900 :=
  five_le_a_of_five_mem (n := 6900) (q1 := 17) (q2 := 59) (q3 := 67) (q4 := 71) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6906 : 5 ≤ a 6906 :=
  five_le_a_of_five_mem (n := 6906) (q1 := 43) (q2 := 113) (q3 := 173) (q4 := 197) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6912 : 5 ≤ a 6912 :=
  five_le_a_of_five_mem (n := 6912) (q1 := 5) (q2 := 71) (q3 := 79) (q4 := 89) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6918 : 5 ≤ a 6918 :=
  five_le_a_of_five_mem (n := 6918) (q1 := 139) (q2 := 311) (q3 := 389) (q4 := 619) (q5 := 631)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6924 : 5 ≤ a 6924 :=
  five_le_a_of_five_mem (n := 6924) (q1 := 53) (q2 := 67) (q3 := 263) (q4 := 373) (q5 := 557)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6930 : 5 ≤ a 6930 :=
  five_le_a_of_five_mem (n := 6930) (q1 := 19) (q2 := 31) (q3 := 47) (q4 := 61) (q5 := 67)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6936 : 5 ≤ a 6936 :=
  five_le_a_of_five_mem (n := 6936) (q1 := 103) (q2 := 107) (q3 := 173) (q4 := 257) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6942 : 5 ≤ a 6942 :=
  five_le_a_of_five_mem (n := 6942) (q1 := 59) (q2 := 71) (q3 := 101) (q4 := 179) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6948 : 5 ≤ a 6948 :=
  five_le_a_of_five_mem (n := 6948) (q1 := 79) (q2 := 211) (q3 := 229) (q4 := 239) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6954 : 5 ≤ a 6954 :=
  five_le_a_of_five_mem (n := 6954) (q1 := 5) (q2 := 7) (q3 := 37) (q4 := 43) (q5 := 47)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6960 : 5 ≤ a 6960 :=
  five_le_a_of_five_mem (n := 6960) (q1 := 11) (q2 := 53) (q3 := 97) (q4 := 167) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6966 : 5 ≤ a 6966 :=
  five_le_a_of_five_mem (n := 6966) (q1 := 5) (q2 := 17) (q3 := 103) (q4 := 137) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6972 : 5 ≤ a 6972 :=
  five_le_a_of_five_mem (n := 6972) (q1 := 5) (q2 := 11) (q3 := 131) (q4 := 149) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6978 : 5 ≤ a 6978 :=
  five_le_a_of_five_mem (n := 6978) (q1 := 19) (q2 := 61) (q3 := 79) (q4 := 149) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6984 : 5 ≤ a 6984 :=
  five_le_a_of_five_mem (n := 6984) (q1 := 7) (q2 := 13) (q3 := 17) (q4 := 73) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6990 : 5 ≤ a 6990 :=
  five_le_a_of_five_mem (n := 6990) (q1 := 7) (q2 := 23) (q3 := 29) (q4 := 79) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_6996 : 5 ≤ a 6996 :=
  five_le_a_of_five_mem (n := 6996) (q1 := 5) (q2 := 47) (q3 := 113) (q4 := 163) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7002 : 5 ≤ a 7002 :=
  five_le_a_of_five_mem (n := 7002) (q1 := 11) (q2 := 41) (q3 := 211) (q4 := 241) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7008 : 5 ≤ a 7008 :=
  five_le_a_of_five_mem (n := 7008) (q1 := 11) (q2 := 31) (q3 := 61) (q4 := 101) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7014 : 5 ≤ a 7014 :=
  five_le_a_of_five_mem (n := 7014) (q1 := 13) (q2 := 43) (q3 := 107) (q4 := 173) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7020 : 5 ≤ a 7020 :=
  five_le_a_of_five_mem (n := 7020) (q1 := 7) (q2 := 19) (q3 := 23) (q4 := 37) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7026 : 5 ≤ a 7026 :=
  five_le_a_of_five_mem (n := 7026) (q1 := 13) (q2 := 43) (q3 := 193) (q4 := 307) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7032 : 5 ≤ a 7032 :=
  five_le_a_of_five_mem (n := 7032) (q1 := 71) (q2 := 251) (q3 := 379) (q4 := 541) (q5 := 659)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7038 : 5 ≤ a 7038 :=
  five_le_a_of_five_mem (n := 7038) (q1 := 19) (q2 := 41) (q3 := 71) (q4 := 89) (q5 := 139)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7044 : 5 ≤ a 7044 :=
  five_le_a_of_five_mem (n := 7044) (q1 := 83) (q2 := 263) (q3 := 307) (q4 := 463) (q5 := 563)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7050 : 5 ≤ a 7050 :=
  five_le_a_of_five_mem (n := 7050) (q1 := 7) (q2 := 53) (q3 := 59) (q4 := 79) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7056 : 5 ≤ a 7056 :=
  five_le_a_of_five_mem (n := 7056) (q1 := 13) (q2 := 73) (q3 := 157) (q4 := 173) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7062 : 5 ≤ a 7062 :=
  five_le_a_of_five_mem (n := 7062) (q1 := 151) (q2 := 191) (q3 := 269) (q4 := 271) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7068 : 5 ≤ a 7068 :=
  five_le_a_of_five_mem (n := 7068) (q1 := 11) (q2 := 41) (q3 := 109) (q4 := 151) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7074 : 5 ≤ a 7074 :=
  five_le_a_of_five_mem (n := 7074) (q1 := 5) (q2 := 47) (q3 := 103) (q4 := 113) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7080 : 5 ≤ a 7080 :=
  five_le_a_of_five_mem (n := 7080) (q1 := 23) (q2 := 41) (q3 := 79) (q4 := 97) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7086 : 5 ≤ a 7086 :=
  five_le_a_of_five_mem (n := 7086) (q1 := 17) (q2 := 43) (q3 := 73) (q4 := 127) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7092 : 5 ≤ a 7092 :=
  five_le_a_of_five_mem (n := 7092) (q1 := 101) (q2 := 229) (q3 := 359) (q4 := 389) (q5 := 431)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7098 : 5 ≤ a 7098 :=
  five_le_a_of_five_mem (n := 7098) (q1 := 29) (q2 := 79) (q3 := 131) (q4 := 139) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7104 : 5 ≤ a 7104 :=
  five_le_a_of_five_mem (n := 7104) (q1 := 47) (q2 := 103) (q3 := 107) (q4 := 193) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7110 : 5 ≤ a 7110 :=
  five_le_a_of_five_mem (n := 7110) (q1 := 41) (q2 := 67) (q3 := 83) (q4 := 97) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7116 : 5 ≤ a 7116 :=
  five_le_a_of_five_mem (n := 7116) (q1 := 13) (q2 := 97) (q3 := 103) (q4 := 167) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7122 : 5 ≤ a 7122 :=
  five_le_a_of_five_mem (n := 7122) (q1 := 131) (q2 := 211) (q3 := 359) (q4 := 419) (q5 := 461)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7128 : 5 ≤ a 7128 :=
  five_le_a_of_five_mem (n := 7128) (q1 := 59) (q2 := 101) (q3 := 109) (q4 := 179) (q5 := 181)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7134 : 5 ≤ a 7134 :=
  five_le_a_of_five_mem (n := 7134) (q1 := 163) (q2 := 173) (q3 := 277) (q4 := 353) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7140 : 5 ≤ a 7140 :=
  five_le_a_of_five_mem (n := 7140) (q1 := 11) (q2 := 19) (q3 := 37) (q4 := 71) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7146 : 5 ≤ a 7146 :=
  five_le_a_of_five_mem (n := 7146) (q1 := 67) (q2 := 107) (q3 := 163) (q4 := 313) (q5 := 353)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7152 : 5 ≤ a 7152 :=
  five_le_a_of_five_mem (n := 7152) (q1 := 181) (q2 := 241) (q3 := 281) (q4 := 389) (q5 := 491)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7158 : 5 ≤ a 7158 :=
  five_le_a_of_five_mem (n := 7158) (q1 := 29) (q2 := 79) (q3 := 89) (q4 := 139) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7164 : 5 ≤ a 7164 :=
  five_le_a_of_five_mem (n := 7164) (q1 := 13) (q2 := 43) (q3 := 167) (q4 := 293) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7170 : 5 ≤ a 7170 :=
  five_le_a_of_five_mem (n := 7170) (q1 := 41) (q2 := 43) (q3 := 67) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7176 : 5 ≤ a 7176 :=
  five_le_a_of_five_mem (n := 7176) (q1 := 17) (q2 := 67) (q3 := 107) (q4 := 157) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7182 : 5 ≤ a 7182 :=
  five_le_a_of_five_mem (n := 7182) (q1 := 5) (q2 := 31) (q3 := 61) (q4 := 139) (q5 := 211)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7188 : 5 ≤ a 7188 :=
  five_le_a_of_five_mem (n := 7188) (q1 := 59) (q2 := 109) (q3 := 229) (q4 := 271) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7194 : 5 ≤ a 7194 :=
  five_le_a_of_five_mem (n := 7194) (q1 := 17) (q2 := 43) (q3 := 137) (q4 := 223) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7200 : 5 ≤ a 7200 :=
  five_le_a_of_five_mem (n := 7200) (q1 := 7) (q2 := 13) (q3 := 97) (q4 := 131) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7206 : 5 ≤ a 7206 :=
  five_le_a_of_five_mem (n := 7206) (q1 := 13) (q2 := 47) (q3 := 103) (q4 := 127) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7212 : 5 ≤ a 7212 :=
  five_le_a_of_five_mem (n := 7212) (q1 := 109) (q2 := 199) (q3 := 349) (q4 := 379) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7218 : 5 ≤ a 7218 :=
  five_le_a_of_five_mem (n := 7218) (q1 := 11) (q2 := 89) (q3 := 199) (q4 := 241) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7224 : 5 ≤ a 7224 :=
  five_le_a_of_five_mem (n := 7224) (q1 := 5) (q2 := 13) (q3 := 73) (q4 := 97) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7230 : 5 ≤ a 7230 :=
  five_le_a_of_five_mem (n := 7230) (q1 := 17) (q2 := 23) (q3 := 53) (q4 := 79) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7236 : 5 ≤ a 7236 :=
  five_le_a_of_five_mem (n := 7236) (q1 := 7) (q2 := 17) (q3 := 157) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7242 : 5 ≤ a 7242 :=
  five_le_a_of_five_mem (n := 7242) (q1 := 5) (q2 := 281) (q3 := 331) (q4 := 379) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7248 : 5 ≤ a 7248 :=
  five_le_a_of_five_mem (n := 7248) (q1 := 5) (q2 := 61) (q3 := 229) (q4 := 251) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7254 : 5 ≤ a 7254 :=
  five_le_a_of_five_mem (n := 7254) (q1 := 43) (q2 := 67) (q3 := 197) (q4 := 227) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7260 : 5 ≤ a 7260 :=
  five_le_a_of_five_mem (n := 7260) (q1 := 23) (q2 := 47) (q3 := 73) (q4 := 109) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7266 : 5 ≤ a 7266 :=
  five_le_a_of_five_mem (n := 7266) (q1 := 223) (q2 := 283) (q3 := 307) (q4 := 317) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7272 : 5 ≤ a 7272 :=
  five_le_a_of_five_mem (n := 7272) (q1 := 59) (q2 := 61) (q3 := 79) (q4 := 311) (q5 := 401)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7278 : 5 ≤ a 7278 :=
  five_le_a_of_five_mem (n := 7278) (q1 := 31) (q2 := 71) (q3 := 199) (q4 := 239) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7284 : 5 ≤ a 7284 :=
  five_le_a_of_five_mem (n := 7284) (q1 := 37) (q2 := 47) (q3 := 257) (q4 := 293) (q5 := 307)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7290 : 5 ≤ a 7290 :=
  five_le_a_of_five_mem (n := 7290) (q1 := 7) (q2 := 43) (q3 := 61) (q4 := 79) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7296 : 5 ≤ a 7296 :=
  five_le_a_of_five_mem (n := 7296) (q1 := 13) (q2 := 53) (q3 := 137) (q4 := 193) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7302 : 5 ≤ a 7302 :=
  five_le_a_of_five_mem (n := 7302) (q1 := 5) (q2 := 19) (q3 := 109) (q4 := 439) (q5 := 521)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7308 : 5 ≤ a 7308 :=
  five_le_a_of_five_mem (n := 7308) (q1 := 61) (q2 := 149) (q3 := 179) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7314 : 5 ≤ a 7314 :=
  five_le_a_of_five_mem (n := 7314) (q1 := 7) (q2 := 17) (q3 := 103) (q4 := 137) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7320 : 5 ≤ a 7320 :=
  five_le_a_of_five_mem (n := 7320) (q1 := 11) (q2 := 13) (q3 := 73) (q4 := 113) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7326 : 5 ≤ a 7326 :=
  five_le_a_of_five_mem (n := 7326) (q1 := 5) (q2 := 43) (q3 := 107) (q4 := 197) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7332 : 5 ≤ a 7332 :=
  five_le_a_of_five_mem (n := 7332) (q1 := 79) (q2 := 229) (q3 := 349) (q4 := 421) (q5 := 461)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7338 : 5 ≤ a 7338 :=
  five_le_a_of_five_mem (n := 7338) (q1 := 31) (q2 := 151) (q3 := 179) (q4 := 211) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7344 : 5 ≤ a 7344 :=
  five_le_a_of_five_mem (n := 7344) (q1 := 107) (q2 := 137) (q3 := 193) (q4 := 347) (q5 := 373)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7350 : 5 ≤ a 7350 :=
  five_le_a_of_five_mem (n := 7350) (q1 := 19) (q2 := 43) (q3 := 67) (q4 := 107) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7356 : 5 ≤ a 7356 :=
  five_le_a_of_five_mem (n := 7356) (q1 := 103) (q2 := 227) (q3 := 313) (q4 := 317) (q5 := 397)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7362 : 5 ≤ a 7362 :=
  five_le_a_of_five_mem (n := 7362) (q1 := 31) (q2 := 211) (q3 := 241) (q4 := 379) (q5 := 479)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7368 : 5 ≤ a 7368 :=
  five_le_a_of_five_mem (n := 7368) (q1 := 131) (q2 := 139) (q3 := 149) (q4 := 181) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7374 : 5 ≤ a 7374 :=
  five_le_a_of_five_mem (n := 7374) (q1 := 43) (q2 := 163) (q3 := 167) (q4 := 317) (q5 := 383)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7380 : 5 ≤ a 7380 :=
  five_le_a_of_five_mem (n := 7380) (q1 := 31) (q2 := 71) (q3 := 97) (q4 := 127) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7386 : 5 ≤ a 7386 :=
  five_le_a_of_five_mem (n := 7386) (q1 := 103) (q2 := 173) (q3 := 257) (q4 := 283) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7392 : 5 ≤ a 7392 :=
  five_le_a_of_five_mem (n := 7392) (q1 := 41) (q2 := 59) (q3 := 149) (q4 := 181) (q5 := 199)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7398 : 5 ≤ a 7398 :=
  five_le_a_of_five_mem (n := 7398) (q1 := 89) (q2 := 101) (q3 := 151) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7404 : 5 ≤ a 7404 :=
  five_le_a_of_five_mem (n := 7404) (q1 := 53) (q2 := 73) (q3 := 83) (q4 := 157) (q5 := 277)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7410 : 5 ≤ a 7410 :=
  five_le_a_of_five_mem (n := 7410) (q1 := 41) (q2 := 79) (q3 := 89) (q4 := 113) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7416 : 5 ≤ a 7416 :=
  five_le_a_of_five_mem (n := 7416) (q1 := 83) (q2 := 107) (q3 := 173) (q4 := 223) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7422 : 5 ≤ a 7422 :=
  five_le_a_of_five_mem (n := 7422) (q1 := 11) (q2 := 29) (q3 := 101) (q4 := 139) (q5 := 431)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7428 : 5 ≤ a 7428 :=
  five_le_a_of_five_mem (n := 7428) (q1 := 59) (q2 := 79) (q3 := 131) (q4 := 241) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7434 : 5 ≤ a 7434 :=
  five_le_a_of_five_mem (n := 7434) (q1 := 17) (q2 := 23) (q3 := 83) (q4 := 103) (q5 := 113)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7440 : 5 ≤ a 7440 :=
  five_le_a_of_five_mem (n := 7440) (q1 := 47) (q2 := 89) (q3 := 107) (q4 := 109) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7446 : 5 ≤ a 7446 :=
  five_le_a_of_five_mem (n := 7446) (q1 := 13) (q2 := 53) (q3 := 113) (q4 := 137) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7452 : 5 ≤ a 7452 :=
  five_le_a_of_five_mem (n := 7452) (q1 := 131) (q2 := 239) (q3 := 541) (q4 := 659) (q5 := 719)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7458 : 5 ≤ a 7458 :=
  five_le_a_of_five_mem (n := 7458) (q1 := 41) (q2 := 89) (q3 := 149) (q4 := 211) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7464 : 5 ≤ a 7464 :=
  five_le_a_of_five_mem (n := 7464) (q1 := 13) (q2 := 53) (q3 := 113) (q4 := 157) (q5 := 227)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7470 : 5 ≤ a 7470 :=
  five_le_a_of_five_mem (n := 7470) (q1 := 11) (q2 := 19) (q3 := 37) (q4 := 53) (q5 := 59)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7476 : 5 ≤ a 7476 :=
  five_le_a_of_five_mem (n := 7476) (q1 := 83) (q2 := 107) (q3 := 127) (q4 := 167) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7482 : 5 ≤ a 7482 :=
  five_le_a_of_five_mem (n := 7482) (q1 := 5) (q2 := 199) (q3 := 271) (q4 := 571) (q5 := 599)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7488 : 5 ≤ a 7488 :=
  five_le_a_of_five_mem (n := 7488) (q1 := 11) (q2 := 29) (q3 := 71) (q4 := 181) (q5 := 269)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7494 : 5 ≤ a 7494 :=
  five_le_a_of_five_mem (n := 7494) (q1 := 5) (q2 := 13) (q3 := 43) (q4 := 83) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7500 : 5 ≤ a 7500 :=
  five_le_a_of_five_mem (n := 7500) (q1 := 23) (q2 := 41) (q3 := 83) (q4 := 89) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7506 : 5 ≤ a 7506 :=
  five_le_a_of_five_mem (n := 7506) (q1 := 17) (q2 := 137) (q3 := 197) (q4 := 347) (q5 := 487)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7512 : 5 ≤ a 7512 :=
  five_le_a_of_five_mem (n := 7512) (q1 := 5) (q2 := 61) (q3 := 79) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7518 : 5 ≤ a 7518 :=
  five_le_a_of_five_mem (n := 7518) (q1 := 11) (q2 := 19) (q3 := 29) (q4 := 31) (q5 := 41)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7524 : 5 ≤ a 7524 :=
  five_le_a_of_five_mem (n := 7524) (q1 := 17) (q2 := 37) (q3 := 67) (q4 := 193) (q5 := 317)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7530 : 5 ≤ a 7530 :=
  five_le_a_of_five_mem (n := 7530) (q1 := 7) (q2 := 31) (q3 := 43) (q4 := 53) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7536 : 5 ≤ a 7536 :=
  five_le_a_of_five_mem (n := 7536) (q1 := 13) (q2 := 37) (q3 := 47) (q4 := 103) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7542 : 5 ≤ a 7542 :=
  five_le_a_of_five_mem (n := 7542) (q1 := 5) (q2 := 19) (q3 := 61) (q4 := 131) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7548 : 5 ≤ a 7548 :=
  five_le_a_of_five_mem (n := 7548) (q1 := 11) (q2 := 41) (q3 := 59) (q4 := 179) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7554 : 5 ≤ a 7554 :=
  five_le_a_of_five_mem (n := 7554) (q1 := 5) (q2 := 7) (q3 := 37) (q4 := 67) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7560 : 5 ≤ a 7560 :=
  five_le_a_of_five_mem (n := 7560) (q1 := 13) (q2 := 23) (q3 := 31) (q4 := 43) (q5 := 61)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7566 : 5 ≤ a 7566 :=
  five_le_a_of_five_mem (n := 7566) (q1 := 7) (q2 := 17) (q3 := 37) (q4 := 107) (q5 := 257)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7572 : 5 ≤ a 7572 :=
  five_le_a_of_five_mem (n := 7572) (q1 := 11) (q2 := 31) (q3 := 251) (q4 := 379) (q5 := 421)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7578 : 5 ≤ a 7578 :=
  five_le_a_of_five_mem (n := 7578) (q1 := 5) (q2 := 29) (q3 := 61) (q4 := 71) (q5 := 349)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7584 : 5 ≤ a 7584 :=
  five_le_a_of_five_mem (n := 7584) (q1 := 7) (q2 := 23) (q3 := 37) (q4 := 97) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7590 : 5 ≤ a 7590 :=
  five_le_a_of_five_mem (n := 7590) (q1 := 13) (q2 := 17) (q3 := 31) (q4 := 53) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7596 : 5 ≤ a 7596 :=
  five_le_a_of_five_mem (n := 7596) (q1 := 7) (q2 := 47) (q3 := 73) (q4 := 107) (q5 := 163)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7602 : 5 ≤ a 7602 :=
  five_le_a_of_five_mem (n := 7602) (q1 := 19) (q2 := 41) (q3 := 79) (q4 := 151) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7608 : 5 ≤ a 7608 :=
  five_le_a_of_five_mem (n := 7608) (q1 := 31) (q2 := 61) (q3 := 79) (q4 := 109) (q5 := 149)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7614 : 5 ≤ a 7614 :=
  five_le_a_of_five_mem (n := 7614) (q1 := 7) (q2 := 67) (q3 := 73) (q4 := 127) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7620 : 5 ≤ a 7620 :=
  five_le_a_of_five_mem (n := 7620) (q1 := 29) (q2 := 61) (q3 := 71) (q4 := 79) (q5 := 83)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7626 : 5 ≤ a 7626 :=
  five_le_a_of_five_mem (n := 7626) (q1 := 23) (q2 := 43) (q3 := 97) (q4 := 127) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7632 : 5 ≤ a 7632 :=
  five_le_a_of_five_mem (n := 7632) (q1 := 11) (q2 := 41) (q3 := 59) (q4 := 71) (q5 := 109)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7638 : 5 ≤ a 7638 :=
  five_le_a_of_five_mem (n := 7638) (q1 := 31) (q2 := 61) (q3 := 79) (q4 := 89) (q5 := 151)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7644 : 5 ≤ a 7644 :=
  five_le_a_of_five_mem (n := 7644) (q1 := 5) (q2 := 37) (q3 := 83) (q4 := 97) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7650 : 5 ≤ a 7650 :=
  five_le_a_of_five_mem (n := 7650) (q1 := 67) (q2 := 73) (q3 := 103) (q4 := 109) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7656 : 5 ≤ a 7656 :=
  five_le_a_of_five_mem (n := 7656) (q1 := 13) (q2 := 17) (q3 := 67) (q4 := 97) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7662 : 5 ≤ a 7662 :=
  five_le_a_of_five_mem (n := 7662) (q1 := 19) (q2 := 41) (q3 := 79) (q4 := 211) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7668 : 5 ≤ a 7668 :=
  five_le_a_of_five_mem (n := 7668) (q1 := 19) (q2 := 211) (q3 := 251) (q4 := 421) (q5 := 449)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7674 : 5 ≤ a 7674 :=
  five_le_a_of_five_mem (n := 7674) (q1 := 53) (q2 := 67) (q3 := 83) (q4 := 167) (q5 := 193)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7680 : 5 ≤ a 7680 :=
  five_le_a_of_five_mem (n := 7680) (q1 := 7) (q2 := 11) (q3 := 37) (q4 := 73) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7686 : 5 ≤ a 7686 :=
  five_le_a_of_five_mem (n := 7686) (q1 := 5) (q2 := 13) (q3 := 17) (q4 := 37) (q5 := 103)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7692 : 5 ≤ a 7692 :=
  five_le_a_of_five_mem (n := 7692) (q1 := 11) (q2 := 101) (q3 := 131) (q4 := 241) (q5 := 409)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7698 : 5 ≤ a 7698 :=
  five_le_a_of_five_mem (n := 7698) (q1 := 29) (q2 := 59) (q3 := 181) (q4 := 239) (q5 := 389)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7704 : 5 ≤ a 7704 :=
  five_le_a_of_five_mem (n := 7704) (q1 := 13) (q2 := 23) (q3 := 113) (q4 := 163) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7710 : 5 ≤ a 7710 :=
  five_le_a_of_five_mem (n := 7710) (q1 := 7) (q2 := 107) (q3 := 163) (q4 := 173) (q5 := 223)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7716 : 5 ≤ a 7716 :=
  five_le_a_of_five_mem (n := 7716) (q1 := 43) (q2 := 73) (q3 := 113) (q4 := 157) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7722 : 5 ≤ a 7722 :=
  five_le_a_of_five_mem (n := 7722) (q1 := 5) (q2 := 19) (q3 := 31) (q4 := 101) (q5 := 131)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7728 : 5 ≤ a 7728 :=
  five_le_a_of_five_mem (n := 7728) (q1 := 29) (q2 := 89) (q3 := 139) (q4 := 151) (q5 := 179)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7734 : 5 ≤ a 7734 :=
  five_le_a_of_five_mem (n := 7734) (q1 := 7) (q2 := 173) (q3 := 193) (q4 := 277) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7740 : 5 ≤ a 7740 :=
  five_le_a_of_five_mem (n := 7740) (q1 := 13) (q2 := 17) (q3 := 53) (q4 := 101) (q5 := 137)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7746 : 5 ≤ a 7746 :=
  five_le_a_of_five_mem (n := 7746) (q1 := 43) (q2 := 47) (q3 := 107) (q4 := 173) (q5 := 313)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7752 : 5 ≤ a 7752 :=
  five_le_a_of_five_mem (n := 7752) (q1 := 71) (q2 := 131) (q3 := 149) (q4 := 211) (q5 := 359)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7758 : 5 ≤ a 7758 :=
  five_le_a_of_five_mem (n := 7758) (q1 := 31) (q2 := 59) (q3 := 71) (q4 := 109) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7764 : 5 ≤ a 7764 :=
  five_le_a_of_five_mem (n := 7764) (q1 := 173) (q2 := 347) (q3 := 353) (q4 := 457) (q5 := 467)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7770 : 5 ≤ a 7770 :=
  five_le_a_of_five_mem (n := 7770) (q1 := 47) (q2 := 53) (q3 := 71) (q4 := 83) (q5 := 97)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7776 : 5 ≤ a 7776 :=
  five_le_a_of_five_mem (n := 7776) (q1 := 17) (q2 := 53) (q3 := 103) (q4 := 107) (q5 := 173)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7782 : 5 ≤ a 7782 :=
  five_le_a_of_five_mem (n := 7782) (q1 := 41) (q2 := 59) (q3 := 101) (q4 := 389) (q5 := 449)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7788 : 5 ≤ a 7788 :=
  five_le_a_of_five_mem (n := 7788) (q1 := 29) (q2 := 89) (q3 := 139) (q4 := 149) (q5 := 229)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7794 : 5 ≤ a 7794 :=
  five_le_a_of_five_mem (n := 7794) (q1 := 107) (q2 := 113) (q3 := 307) (q4 := 317) (q5 := 443)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7800 : 5 ≤ a 7800 :=
  five_le_a_of_five_mem (n := 7800) (q1 := 41) (q2 := 73) (q3 := 83) (q4 := 101) (q5 := 127)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7806 : 5 ≤ a 7806 :=
  five_le_a_of_five_mem (n := 7806) (q1 := 17) (q2 := 47) (q3 := 157) (q4 := 233) (q5 := 283)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7812 : 5 ≤ a 7812 :=
  five_le_a_of_five_mem (n := 7812) (q1 := 71) (q2 := 89) (q3 := 139) (q4 := 379) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7818 : 5 ≤ a 7818 :=
  five_le_a_of_five_mem (n := 7818) (q1 := 59) (q2 := 61) (q3 := 101) (q4 := 131) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7824 : 5 ≤ a 7824 :=
  five_le_a_of_five_mem (n := 7824) (q1 := 83) (q2 := 263) (q3 := 277) (q4 := 337) (q5 := 347)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7830 : 5 ≤ a 7830 :=
  five_le_a_of_five_mem (n := 7830) (q1 := 37) (q2 := 71) (q3 := 89) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7836 : 5 ≤ a 7836 :=
  five_le_a_of_five_mem (n := 7836) (q1 := 43) (q2 := 47) (q3 := 83) (q4 := 113) (q5 := 233)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7842 : 5 ≤ a 7842 :=
  five_le_a_of_five_mem (n := 7842) (q1 := 151) (q2 := 239) (q3 := 251) (q4 := 269) (q5 := 281)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7848 : 5 ≤ a 7848 :=
  five_le_a_of_five_mem (n := 7848) (q1 := 19) (q2 := 31) (q3 := 59) (q4 := 89) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7854 : 5 ≤ a 7854 :=
  five_le_a_of_five_mem (n := 7854) (q1 := 13) (q2 := 97) (q3 := 163) (q4 := 233) (q5 := 263)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7860 : 5 ≤ a 7860 :=
  five_le_a_of_five_mem (n := 7860) (q1 := 7) (q2 := 19) (q3 := 67) (q4 := 103) (q5 := 157)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7866 : 5 ≤ a 7866 :=
  five_le_a_of_five_mem (n := 7866) (q1 := 13) (q2 := 193) (q3 := 223) (q4 := 227) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7872 : 5 ≤ a 7872 :=
  five_le_a_of_five_mem (n := 7872) (q1 := 5) (q2 := 79) (q3 := 181) (q4 := 229) (q5 := 251)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7878 : 5 ≤ a 7878 :=
  five_le_a_of_five_mem (n := 7878) (q1 := 5) (q2 := 191) (q3 := 239) (q4 := 331) (q5 := 419)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7884 : 5 ≤ a 7884 :=
  five_le_a_of_five_mem (n := 7884) (q1 := 17) (q2 := 43) (q3 := 67) (q4 := 127) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7890 : 5 ≤ a 7890 :=
  five_le_a_of_five_mem (n := 7890) (q1 := 11) (q2 := 17) (q3 := 37) (q4 := 61) (q5 := 73)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7896 : 5 ≤ a 7896 :=
  five_le_a_of_five_mem (n := 7896) (q1 := 23) (q2 := 67) (q3 := 173) (q4 := 193) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7902 : 5 ≤ a 7902 :=
  five_le_a_of_five_mem (n := 7902) (q1 := 61) (q2 := 109) (q3 := 179) (q4 := 199) (q5 := 619)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7908 : 5 ≤ a 7908 :=
  five_le_a_of_five_mem (n := 7908) (q1 := 29) (q2 := 41) (q3 := 151) (q4 := 181) (q5 := 239)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7914 : 5 ≤ a 7914 :=
  five_le_a_of_five_mem (n := 7914) (q1 := 13) (q2 := 37) (q3 := 97) (q4 := 173) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7920 : 5 ≤ a 7920 :=
  five_le_a_of_five_mem (n := 7920) (q1 := 13) (q2 := 43) (q3 := 97) (q4 := 167) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7926 : 5 ≤ a 7926 :=
  five_le_a_of_five_mem (n := 7926) (q1 := 7) (q2 := 167) (q3 := 283) (q4 := 337) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7932 : 5 ≤ a 7932 :=
  five_le_a_of_five_mem (n := 7932) (q1 := 5) (q2 := 31) (q3 := 79) (q4 := 179) (q5 := 191)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7938 : 5 ≤ a 7938 :=
  five_le_a_of_five_mem (n := 7938) (q1 := 11) (q2 := 71) (q3 := 149) (q4 := 179) (q5 := 331)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7944 : 5 ≤ a 7944 :=
  five_le_a_of_five_mem (n := 7944) (q1 := 7) (q2 := 67) (q3 := 227) (q4 := 353) (q5 := 367)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7950 : 5 ≤ a 7950 :=
  five_le_a_of_five_mem (n := 7950) (q1 := 13) (q2 := 43) (q3 := 67) (q4 := 109) (q5 := 197)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7956 : 5 ≤ a 7956 :=
  five_le_a_of_five_mem (n := 7956) (q1 := 7) (q2 := 37) (q3 := 83) (q4 := 103) (q5 := 167)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7962 : 5 ≤ a 7962 :=
  five_le_a_of_five_mem (n := 7962) (q1 := 139) (q2 := 271) (q3 := 281) (q4 := 401) (q5 := 719)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7968 : 5 ≤ a 7968 :=
  five_le_a_of_five_mem (n := 7968) (q1 := 41) (q2 := 101) (q3 := 179) (q4 := 211) (q5 := 241)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7974 : 5 ≤ a 7974 :=
  five_le_a_of_five_mem (n := 7974) (q1 := 37) (q2 := 107) (q3 := 257) (q4 := 457) (q5 := 487)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7980 : 5 ≤ a 7980 :=
  five_le_a_of_five_mem (n := 7980) (q1 := 29) (q2 := 31) (q3 := 73) (q4 := 79) (q5 := 101)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7986 : 5 ≤ a 7986 :=
  five_le_a_of_five_mem (n := 7986) (q1 := 23) (q2 := 53) (q3 := 67) (q4 := 103) (q5 := 107)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7992 : 5 ≤ a 7992 :=
  five_le_a_of_five_mem (n := 7992) (q1 := 109) (q2 := 199) (q3 := 239) (q4 := 251) (q5 := 431)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_7998 : 5 ≤ a 7998 :=
  five_le_a_of_five_mem (n := 7998) (q1 := 61) (q2 := 71) (q3 := 181) (q4 := 239) (q5 := 271)
    (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset) (by prove_in_Sset)
    (by decide)

lemma five_le_a_chunk_0 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 24 ≤ n) (hle : n ≤ 168) : 5 ≤ a n := by
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
  else if h : n = 144 then
    subst h; exact five_le_a_144
  else if h : n = 150 then
    subst h; exact five_le_a_150
  else if h : n = 156 then
    subst h; exact five_le_a_156
  else if h : n = 162 then
    subst h; exact five_le_a_162
  else if h : n = 168 then
    subst h; exact five_le_a_168
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_1 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 174 ≤ n) (hle : n ≤ 318) : 5 ≤ a n := by
  if h : n = 174 then
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
  else if h : n = 264 then
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
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_2 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 324 ≤ n) (hle : n ≤ 468) : 5 ≤ a n := by
  if h : n = 324 then
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
  else if h : n = 384 then
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
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_3 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 474 ≤ n) (hle : n ≤ 618) : 5 ≤ a n := by
  if h : n = 474 then
    subst h; exact five_le_a_474
  else if h : n = 480 then
    subst h; exact five_le_a_480
  else if h : n = 486 then
    subst h; exact five_le_a_486
  else if h : n = 492 then
    subst h; exact five_le_a_492
  else if h : n = 498 then
    subst h; exact five_le_a_498
  else if h : n = 504 then
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

lemma five_le_a_chunk_4 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 624 ≤ n) (hle : n ≤ 768) : 5 ≤ a n := by
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
  else if h : n = 744 then
    subst h; exact five_le_a_744
  else if h : n = 750 then
    subst h; exact five_le_a_750
  else if h : n = 756 then
    subst h; exact five_le_a_756
  else if h : n = 762 then
    subst h; exact five_le_a_762
  else if h : n = 768 then
    subst h; exact five_le_a_768
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_5 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 774 ≤ n) (hle : n ≤ 918) : 5 ≤ a n := by
  if h : n = 774 then
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
  else if h : n = 864 then
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
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_6 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 924 ≤ n) (hle : n ≤ 1068) : 5 ≤ a n := by
  if h : n = 924 then
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
  else if h : n = 984 then
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
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_7 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1074 ≤ n) (hle : n ≤ 1218) : 5 ≤ a n := by
  if h : n = 1074 then
    subst h; exact five_le_a_1074
  else if h : n = 1080 then
    subst h; exact five_le_a_1080
  else if h : n = 1086 then
    subst h; exact five_le_a_1086
  else if h : n = 1092 then
    subst h; exact five_le_a_1092
  else if h : n = 1098 then
    subst h; exact five_le_a_1098
  else if h : n = 1104 then
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
  else if h : n = 1206 then
    subst h; exact five_le_a_1206
  else if h : n = 1212 then
    subst h; exact five_le_a_1212
  else if h : n = 1218 then
    subst h; exact five_le_a_1218
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_8 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1224 ≤ n) (hle : n ≤ 1368) : 5 ≤ a n := by
  if h : n = 1224 then
    subst h; exact five_le_a_1224
  else if h : n = 1230 then
    subst h; exact five_le_a_1230
  else if h : n = 1236 then
    subst h; exact five_le_a_1236
  else if h : n = 1242 then
    subst h; exact five_le_a_1242
  else if h : n = 1248 then
    subst h; exact five_le_a_1248
  else if h : n = 1254 then
    subst h; exact five_le_a_1254
  else if h : n = 1260 then
    subst h; exact five_le_a_1260
  else if h : n = 1266 then
    subst h; exact five_le_a_1266
  else if h : n = 1272 then
    subst h; exact five_le_a_1272
  else if h : n = 1278 then
    subst h; exact five_le_a_1278
  else if h : n = 1284 then
    subst h; exact five_le_a_1284
  else if h : n = 1290 then
    subst h; exact five_le_a_1290
  else if h : n = 1296 then
    subst h; exact five_le_a_1296
  else if h : n = 1302 then
    subst h; exact five_le_a_1302
  else if h : n = 1308 then
    subst h; exact five_le_a_1308
  else if h : n = 1314 then
    subst h; exact five_le_a_1314
  else if h : n = 1320 then
    subst h; exact five_le_a_1320
  else if h : n = 1326 then
    subst h; exact five_le_a_1326
  else if h : n = 1332 then
    subst h; exact five_le_a_1332
  else if h : n = 1338 then
    subst h; exact five_le_a_1338
  else if h : n = 1344 then
    subst h; exact five_le_a_1344
  else if h : n = 1350 then
    subst h; exact five_le_a_1350
  else if h : n = 1356 then
    subst h; exact five_le_a_1356
  else if h : n = 1362 then
    subst h; exact five_le_a_1362
  else if h : n = 1368 then
    subst h; exact five_le_a_1368
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_9 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1374 ≤ n) (hle : n ≤ 1518) : 5 ≤ a n := by
  if h : n = 1374 then
    subst h; exact five_le_a_1374
  else if h : n = 1380 then
    subst h; exact five_le_a_1380
  else if h : n = 1386 then
    subst h; exact five_le_a_1386
  else if h : n = 1392 then
    subst h; exact five_le_a_1392
  else if h : n = 1398 then
    subst h; exact five_le_a_1398
  else if h : n = 1404 then
    subst h; exact five_le_a_1404
  else if h : n = 1410 then
    subst h; exact five_le_a_1410
  else if h : n = 1416 then
    subst h; exact five_le_a_1416
  else if h : n = 1422 then
    subst h; exact five_le_a_1422
  else if h : n = 1428 then
    subst h; exact five_le_a_1428
  else if h : n = 1434 then
    subst h; exact five_le_a_1434
  else if h : n = 1440 then
    subst h; exact five_le_a_1440
  else if h : n = 1446 then
    subst h; exact five_le_a_1446
  else if h : n = 1452 then
    subst h; exact five_le_a_1452
  else if h : n = 1458 then
    subst h; exact five_le_a_1458
  else if h : n = 1464 then
    subst h; exact five_le_a_1464
  else if h : n = 1470 then
    subst h; exact five_le_a_1470
  else if h : n = 1476 then
    subst h; exact five_le_a_1476
  else if h : n = 1482 then
    subst h; exact five_le_a_1482
  else if h : n = 1488 then
    subst h; exact five_le_a_1488
  else if h : n = 1494 then
    subst h; exact five_le_a_1494
  else if h : n = 1500 then
    subst h; exact five_le_a_1500
  else if h : n = 1506 then
    subst h; exact five_le_a_1506
  else if h : n = 1512 then
    subst h; exact five_le_a_1512
  else if h : n = 1518 then
    subst h; exact five_le_a_1518
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_10 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1524 ≤ n) (hle : n ≤ 1668) : 5 ≤ a n := by
  if h : n = 1524 then
    subst h; exact five_le_a_1524
  else if h : n = 1530 then
    subst h; exact five_le_a_1530
  else if h : n = 1536 then
    subst h; exact five_le_a_1536
  else if h : n = 1542 then
    subst h; exact five_le_a_1542
  else if h : n = 1548 then
    subst h; exact five_le_a_1548
  else if h : n = 1554 then
    subst h; exact five_le_a_1554
  else if h : n = 1560 then
    subst h; exact five_le_a_1560
  else if h : n = 1566 then
    subst h; exact five_le_a_1566
  else if h : n = 1572 then
    subst h; exact five_le_a_1572
  else if h : n = 1578 then
    subst h; exact five_le_a_1578
  else if h : n = 1584 then
    subst h; exact five_le_a_1584
  else if h : n = 1590 then
    subst h; exact five_le_a_1590
  else if h : n = 1596 then
    subst h; exact five_le_a_1596
  else if h : n = 1602 then
    subst h; exact five_le_a_1602
  else if h : n = 1608 then
    subst h; exact five_le_a_1608
  else if h : n = 1614 then
    subst h; exact five_le_a_1614
  else if h : n = 1620 then
    subst h; exact five_le_a_1620
  else if h : n = 1626 then
    subst h; exact five_le_a_1626
  else if h : n = 1632 then
    subst h; exact five_le_a_1632
  else if h : n = 1638 then
    subst h; exact five_le_a_1638
  else if h : n = 1644 then
    subst h; exact five_le_a_1644
  else if h : n = 1650 then
    subst h; exact five_le_a_1650
  else if h : n = 1656 then
    subst h; exact five_le_a_1656
  else if h : n = 1662 then
    subst h; exact five_le_a_1662
  else if h : n = 1668 then
    subst h; exact five_le_a_1668
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_11 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1674 ≤ n) (hle : n ≤ 1818) : 5 ≤ a n := by
  if h : n = 1674 then
    subst h; exact five_le_a_1674
  else if h : n = 1680 then
    subst h; exact five_le_a_1680
  else if h : n = 1686 then
    subst h; exact five_le_a_1686
  else if h : n = 1692 then
    subst h; exact five_le_a_1692
  else if h : n = 1698 then
    subst h; exact five_le_a_1698
  else if h : n = 1704 then
    subst h; exact five_le_a_1704
  else if h : n = 1710 then
    subst h; exact five_le_a_1710
  else if h : n = 1716 then
    subst h; exact five_le_a_1716
  else if h : n = 1722 then
    subst h; exact five_le_a_1722
  else if h : n = 1728 then
    subst h; exact five_le_a_1728
  else if h : n = 1734 then
    subst h; exact five_le_a_1734
  else if h : n = 1740 then
    subst h; exact five_le_a_1740
  else if h : n = 1746 then
    subst h; exact five_le_a_1746
  else if h : n = 1752 then
    subst h; exact five_le_a_1752
  else if h : n = 1758 then
    subst h; exact five_le_a_1758
  else if h : n = 1764 then
    subst h; exact five_le_a_1764
  else if h : n = 1770 then
    subst h; exact five_le_a_1770
  else if h : n = 1776 then
    subst h; exact five_le_a_1776
  else if h : n = 1782 then
    subst h; exact five_le_a_1782
  else if h : n = 1788 then
    subst h; exact five_le_a_1788
  else if h : n = 1794 then
    subst h; exact five_le_a_1794
  else if h : n = 1800 then
    subst h; exact five_le_a_1800
  else if h : n = 1806 then
    subst h; exact five_le_a_1806
  else if h : n = 1812 then
    subst h; exact five_le_a_1812
  else if h : n = 1818 then
    subst h; exact five_le_a_1818
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_12 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1824 ≤ n) (hle : n ≤ 1968) : 5 ≤ a n := by
  if h : n = 1824 then
    subst h; exact five_le_a_1824
  else if h : n = 1830 then
    subst h; exact five_le_a_1830
  else if h : n = 1836 then
    subst h; exact five_le_a_1836
  else if h : n = 1842 then
    subst h; exact five_le_a_1842
  else if h : n = 1848 then
    subst h; exact five_le_a_1848
  else if h : n = 1854 then
    subst h; exact five_le_a_1854
  else if h : n = 1860 then
    subst h; exact five_le_a_1860
  else if h : n = 1866 then
    subst h; exact five_le_a_1866
  else if h : n = 1872 then
    subst h; exact five_le_a_1872
  else if h : n = 1878 then
    subst h; exact five_le_a_1878
  else if h : n = 1884 then
    subst h; exact five_le_a_1884
  else if h : n = 1890 then
    subst h; exact five_le_a_1890
  else if h : n = 1896 then
    subst h; exact five_le_a_1896
  else if h : n = 1902 then
    subst h; exact five_le_a_1902
  else if h : n = 1908 then
    subst h; exact five_le_a_1908
  else if h : n = 1914 then
    subst h; exact five_le_a_1914
  else if h : n = 1920 then
    subst h; exact five_le_a_1920
  else if h : n = 1926 then
    subst h; exact five_le_a_1926
  else if h : n = 1932 then
    subst h; exact five_le_a_1932
  else if h : n = 1938 then
    subst h; exact five_le_a_1938
  else if h : n = 1944 then
    subst h; exact five_le_a_1944
  else if h : n = 1950 then
    subst h; exact five_le_a_1950
  else if h : n = 1956 then
    subst h; exact five_le_a_1956
  else if h : n = 1962 then
    subst h; exact five_le_a_1962
  else if h : n = 1968 then
    subst h; exact five_le_a_1968
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_13 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 1974 ≤ n) (hle : n ≤ 2118) : 5 ≤ a n := by
  if h : n = 1974 then
    subst h; exact five_le_a_1974
  else if h : n = 1980 then
    subst h; exact five_le_a_1980
  else if h : n = 1986 then
    subst h; exact five_le_a_1986
  else if h : n = 1992 then
    subst h; exact five_le_a_1992
  else if h : n = 1998 then
    subst h; exact five_le_a_1998
  else if h : n = 2004 then
    subst h; exact five_le_a_2004
  else if h : n = 2010 then
    subst h; exact five_le_a_2010
  else if h : n = 2016 then
    subst h; exact five_le_a_2016
  else if h : n = 2022 then
    subst h; exact five_le_a_2022
  else if h : n = 2028 then
    subst h; exact five_le_a_2028
  else if h : n = 2034 then
    subst h; exact five_le_a_2034
  else if h : n = 2040 then
    subst h; exact five_le_a_2040
  else if h : n = 2046 then
    subst h; exact five_le_a_2046
  else if h : n = 2052 then
    subst h; exact five_le_a_2052
  else if h : n = 2058 then
    subst h; exact five_le_a_2058
  else if h : n = 2064 then
    subst h; exact five_le_a_2064
  else if h : n = 2070 then
    subst h; exact five_le_a_2070
  else if h : n = 2076 then
    subst h; exact five_le_a_2076
  else if h : n = 2082 then
    subst h; exact five_le_a_2082
  else if h : n = 2088 then
    subst h; exact five_le_a_2088
  else if h : n = 2094 then
    subst h; exact five_le_a_2094
  else if h : n = 2100 then
    subst h; exact five_le_a_2100
  else if h : n = 2106 then
    subst h; exact five_le_a_2106
  else if h : n = 2112 then
    subst h; exact five_le_a_2112
  else if h : n = 2118 then
    subst h; exact five_le_a_2118
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_14 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2124 ≤ n) (hle : n ≤ 2268) : 5 ≤ a n := by
  if h : n = 2124 then
    subst h; exact five_le_a_2124
  else if h : n = 2130 then
    subst h; exact five_le_a_2130
  else if h : n = 2136 then
    subst h; exact five_le_a_2136
  else if h : n = 2142 then
    subst h; exact five_le_a_2142
  else if h : n = 2148 then
    subst h; exact five_le_a_2148
  else if h : n = 2154 then
    subst h; exact five_le_a_2154
  else if h : n = 2160 then
    subst h; exact five_le_a_2160
  else if h : n = 2166 then
    subst h; exact five_le_a_2166
  else if h : n = 2172 then
    subst h; exact five_le_a_2172
  else if h : n = 2178 then
    subst h; exact five_le_a_2178
  else if h : n = 2184 then
    subst h; exact five_le_a_2184
  else if h : n = 2190 then
    subst h; exact five_le_a_2190
  else if h : n = 2196 then
    subst h; exact five_le_a_2196
  else if h : n = 2202 then
    subst h; exact five_le_a_2202
  else if h : n = 2208 then
    subst h; exact five_le_a_2208
  else if h : n = 2214 then
    subst h; exact five_le_a_2214
  else if h : n = 2220 then
    subst h; exact five_le_a_2220
  else if h : n = 2226 then
    subst h; exact five_le_a_2226
  else if h : n = 2232 then
    subst h; exact five_le_a_2232
  else if h : n = 2238 then
    subst h; exact five_le_a_2238
  else if h : n = 2244 then
    subst h; exact five_le_a_2244
  else if h : n = 2250 then
    subst h; exact five_le_a_2250
  else if h : n = 2256 then
    subst h; exact five_le_a_2256
  else if h : n = 2262 then
    subst h; exact five_le_a_2262
  else if h : n = 2268 then
    subst h; exact five_le_a_2268
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_15 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2274 ≤ n) (hle : n ≤ 2418) : 5 ≤ a n := by
  if h : n = 2274 then
    subst h; exact five_le_a_2274
  else if h : n = 2280 then
    subst h; exact five_le_a_2280
  else if h : n = 2286 then
    subst h; exact five_le_a_2286
  else if h : n = 2292 then
    subst h; exact five_le_a_2292
  else if h : n = 2298 then
    subst h; exact five_le_a_2298
  else if h : n = 2304 then
    subst h; exact five_le_a_2304
  else if h : n = 2310 then
    subst h; exact five_le_a_2310
  else if h : n = 2316 then
    subst h; exact five_le_a_2316
  else if h : n = 2322 then
    subst h; exact five_le_a_2322
  else if h : n = 2328 then
    subst h; exact five_le_a_2328
  else if h : n = 2334 then
    subst h; exact five_le_a_2334
  else if h : n = 2340 then
    subst h; exact five_le_a_2340
  else if h : n = 2346 then
    subst h; exact five_le_a_2346
  else if h : n = 2352 then
    subst h; exact five_le_a_2352
  else if h : n = 2358 then
    subst h; exact five_le_a_2358
  else if h : n = 2364 then
    subst h; exact five_le_a_2364
  else if h : n = 2370 then
    subst h; exact five_le_a_2370
  else if h : n = 2376 then
    subst h; exact five_le_a_2376
  else if h : n = 2382 then
    subst h; exact five_le_a_2382
  else if h : n = 2388 then
    subst h; exact five_le_a_2388
  else if h : n = 2394 then
    subst h; exact five_le_a_2394
  else if h : n = 2400 then
    subst h; exact five_le_a_2400
  else if h : n = 2406 then
    subst h; exact five_le_a_2406
  else if h : n = 2412 then
    subst h; exact five_le_a_2412
  else if h : n = 2418 then
    subst h; exact five_le_a_2418
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_16 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2424 ≤ n) (hle : n ≤ 2568) : 5 ≤ a n := by
  if h : n = 2424 then
    subst h; exact five_le_a_2424
  else if h : n = 2430 then
    subst h; exact five_le_a_2430
  else if h : n = 2436 then
    subst h; exact five_le_a_2436
  else if h : n = 2442 then
    subst h; exact five_le_a_2442
  else if h : n = 2448 then
    subst h; exact five_le_a_2448
  else if h : n = 2454 then
    subst h; exact five_le_a_2454
  else if h : n = 2460 then
    subst h; exact five_le_a_2460
  else if h : n = 2466 then
    subst h; exact five_le_a_2466
  else if h : n = 2472 then
    subst h; exact five_le_a_2472
  else if h : n = 2478 then
    subst h; exact five_le_a_2478
  else if h : n = 2484 then
    subst h; exact five_le_a_2484
  else if h : n = 2490 then
    subst h; exact five_le_a_2490
  else if h : n = 2496 then
    subst h; exact five_le_a_2496
  else if h : n = 2502 then
    subst h; exact five_le_a_2502
  else if h : n = 2508 then
    subst h; exact five_le_a_2508
  else if h : n = 2514 then
    subst h; exact five_le_a_2514
  else if h : n = 2520 then
    subst h; exact five_le_a_2520
  else if h : n = 2526 then
    subst h; exact five_le_a_2526
  else if h : n = 2532 then
    subst h; exact five_le_a_2532
  else if h : n = 2538 then
    subst h; exact five_le_a_2538
  else if h : n = 2544 then
    subst h; exact five_le_a_2544
  else if h : n = 2550 then
    subst h; exact five_le_a_2550
  else if h : n = 2556 then
    subst h; exact five_le_a_2556
  else if h : n = 2562 then
    subst h; exact five_le_a_2562
  else if h : n = 2568 then
    subst h; exact five_le_a_2568
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_17 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2574 ≤ n) (hle : n ≤ 2718) : 5 ≤ a n := by
  if h : n = 2574 then
    subst h; exact five_le_a_2574
  else if h : n = 2580 then
    subst h; exact five_le_a_2580
  else if h : n = 2586 then
    subst h; exact five_le_a_2586
  else if h : n = 2592 then
    subst h; exact five_le_a_2592
  else if h : n = 2598 then
    subst h; exact five_le_a_2598
  else if h : n = 2604 then
    subst h; exact five_le_a_2604
  else if h : n = 2610 then
    subst h; exact five_le_a_2610
  else if h : n = 2616 then
    subst h; exact five_le_a_2616
  else if h : n = 2622 then
    subst h; exact five_le_a_2622
  else if h : n = 2628 then
    subst h; exact five_le_a_2628
  else if h : n = 2634 then
    subst h; exact five_le_a_2634
  else if h : n = 2640 then
    subst h; exact five_le_a_2640
  else if h : n = 2646 then
    subst h; exact five_le_a_2646
  else if h : n = 2652 then
    subst h; exact five_le_a_2652
  else if h : n = 2658 then
    subst h; exact five_le_a_2658
  else if h : n = 2664 then
    subst h; exact five_le_a_2664
  else if h : n = 2670 then
    subst h; exact five_le_a_2670
  else if h : n = 2676 then
    subst h; exact five_le_a_2676
  else if h : n = 2682 then
    subst h; exact five_le_a_2682
  else if h : n = 2688 then
    subst h; exact five_le_a_2688
  else if h : n = 2694 then
    subst h; exact five_le_a_2694
  else if h : n = 2700 then
    subst h; exact five_le_a_2700
  else if h : n = 2706 then
    subst h; exact five_le_a_2706
  else if h : n = 2712 then
    subst h; exact five_le_a_2712
  else if h : n = 2718 then
    subst h; exact five_le_a_2718
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_18 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2724 ≤ n) (hle : n ≤ 2868) : 5 ≤ a n := by
  if h : n = 2724 then
    subst h; exact five_le_a_2724
  else if h : n = 2730 then
    subst h; exact five_le_a_2730
  else if h : n = 2736 then
    subst h; exact five_le_a_2736
  else if h : n = 2742 then
    subst h; exact five_le_a_2742
  else if h : n = 2748 then
    subst h; exact five_le_a_2748
  else if h : n = 2754 then
    subst h; exact five_le_a_2754
  else if h : n = 2760 then
    subst h; exact five_le_a_2760
  else if h : n = 2766 then
    subst h; exact five_le_a_2766
  else if h : n = 2772 then
    subst h; exact five_le_a_2772
  else if h : n = 2778 then
    subst h; exact five_le_a_2778
  else if h : n = 2784 then
    subst h; exact five_le_a_2784
  else if h : n = 2790 then
    subst h; exact five_le_a_2790
  else if h : n = 2796 then
    subst h; exact five_le_a_2796
  else if h : n = 2802 then
    subst h; exact five_le_a_2802
  else if h : n = 2808 then
    subst h; exact five_le_a_2808
  else if h : n = 2814 then
    subst h; exact five_le_a_2814
  else if h : n = 2820 then
    subst h; exact five_le_a_2820
  else if h : n = 2826 then
    subst h; exact five_le_a_2826
  else if h : n = 2832 then
    subst h; exact five_le_a_2832
  else if h : n = 2838 then
    subst h; exact five_le_a_2838
  else if h : n = 2844 then
    subst h; exact five_le_a_2844
  else if h : n = 2850 then
    subst h; exact five_le_a_2850
  else if h : n = 2856 then
    subst h; exact five_le_a_2856
  else if h : n = 2862 then
    subst h; exact five_le_a_2862
  else if h : n = 2868 then
    subst h; exact five_le_a_2868
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_19 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 2874 ≤ n) (hle : n ≤ 3018) : 5 ≤ a n := by
  if h : n = 2874 then
    subst h; exact five_le_a_2874
  else if h : n = 2880 then
    subst h; exact five_le_a_2880
  else if h : n = 2886 then
    subst h; exact five_le_a_2886
  else if h : n = 2892 then
    subst h; exact five_le_a_2892
  else if h : n = 2898 then
    subst h; exact five_le_a_2898
  else if h : n = 2904 then
    subst h; exact five_le_a_2904
  else if h : n = 2910 then
    subst h; exact five_le_a_2910
  else if h : n = 2916 then
    subst h; exact five_le_a_2916
  else if h : n = 2922 then
    subst h; exact five_le_a_2922
  else if h : n = 2928 then
    subst h; exact five_le_a_2928
  else if h : n = 2934 then
    subst h; exact five_le_a_2934
  else if h : n = 2940 then
    subst h; exact five_le_a_2940
  else if h : n = 2946 then
    subst h; exact five_le_a_2946
  else if h : n = 2952 then
    subst h; exact five_le_a_2952
  else if h : n = 2958 then
    subst h; exact five_le_a_2958
  else if h : n = 2964 then
    subst h; exact five_le_a_2964
  else if h : n = 2970 then
    subst h; exact five_le_a_2970
  else if h : n = 2976 then
    subst h; exact five_le_a_2976
  else if h : n = 2982 then
    subst h; exact five_le_a_2982
  else if h : n = 2988 then
    subst h; exact five_le_a_2988
  else if h : n = 2994 then
    subst h; exact five_le_a_2994
  else if h : n = 3000 then
    subst h; exact five_le_a_3000
  else if h : n = 3006 then
    subst h; exact five_le_a_3006
  else if h : n = 3012 then
    subst h; exact five_le_a_3012
  else if h : n = 3018 then
    subst h; exact five_le_a_3018
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_20 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3024 ≤ n) (hle : n ≤ 3168) : 5 ≤ a n := by
  if h : n = 3024 then
    subst h; exact five_le_a_3024
  else if h : n = 3030 then
    subst h; exact five_le_a_3030
  else if h : n = 3036 then
    subst h; exact five_le_a_3036
  else if h : n = 3042 then
    subst h; exact five_le_a_3042
  else if h : n = 3048 then
    subst h; exact five_le_a_3048
  else if h : n = 3054 then
    subst h; exact five_le_a_3054
  else if h : n = 3060 then
    subst h; exact five_le_a_3060
  else if h : n = 3066 then
    subst h; exact five_le_a_3066
  else if h : n = 3072 then
    subst h; exact five_le_a_3072
  else if h : n = 3078 then
    subst h; exact five_le_a_3078
  else if h : n = 3084 then
    subst h; exact five_le_a_3084
  else if h : n = 3090 then
    subst h; exact five_le_a_3090
  else if h : n = 3096 then
    subst h; exact five_le_a_3096
  else if h : n = 3102 then
    subst h; exact five_le_a_3102
  else if h : n = 3108 then
    subst h; exact five_le_a_3108
  else if h : n = 3114 then
    subst h; exact five_le_a_3114
  else if h : n = 3120 then
    subst h; exact five_le_a_3120
  else if h : n = 3126 then
    subst h; exact five_le_a_3126
  else if h : n = 3132 then
    subst h; exact five_le_a_3132
  else if h : n = 3138 then
    subst h; exact five_le_a_3138
  else if h : n = 3144 then
    subst h; exact five_le_a_3144
  else if h : n = 3150 then
    subst h; exact five_le_a_3150
  else if h : n = 3156 then
    subst h; exact five_le_a_3156
  else if h : n = 3162 then
    subst h; exact five_le_a_3162
  else if h : n = 3168 then
    subst h; exact five_le_a_3168
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_21 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3174 ≤ n) (hle : n ≤ 3318) : 5 ≤ a n := by
  if h : n = 3174 then
    subst h; exact five_le_a_3174
  else if h : n = 3180 then
    subst h; exact five_le_a_3180
  else if h : n = 3186 then
    subst h; exact five_le_a_3186
  else if h : n = 3192 then
    subst h; exact five_le_a_3192
  else if h : n = 3198 then
    subst h; exact five_le_a_3198
  else if h : n = 3204 then
    subst h; exact five_le_a_3204
  else if h : n = 3210 then
    subst h; exact five_le_a_3210
  else if h : n = 3216 then
    subst h; exact five_le_a_3216
  else if h : n = 3222 then
    subst h; exact five_le_a_3222
  else if h : n = 3228 then
    subst h; exact five_le_a_3228
  else if h : n = 3234 then
    subst h; exact five_le_a_3234
  else if h : n = 3240 then
    subst h; exact five_le_a_3240
  else if h : n = 3246 then
    subst h; exact five_le_a_3246
  else if h : n = 3252 then
    subst h; exact five_le_a_3252
  else if h : n = 3258 then
    subst h; exact five_le_a_3258
  else if h : n = 3264 then
    subst h; exact five_le_a_3264
  else if h : n = 3270 then
    subst h; exact five_le_a_3270
  else if h : n = 3276 then
    subst h; exact five_le_a_3276
  else if h : n = 3282 then
    subst h; exact five_le_a_3282
  else if h : n = 3288 then
    subst h; exact five_le_a_3288
  else if h : n = 3294 then
    subst h; exact five_le_a_3294
  else if h : n = 3300 then
    subst h; exact five_le_a_3300
  else if h : n = 3306 then
    subst h; exact five_le_a_3306
  else if h : n = 3312 then
    subst h; exact five_le_a_3312
  else if h : n = 3318 then
    subst h; exact five_le_a_3318
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_22 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3324 ≤ n) (hle : n ≤ 3468) : 5 ≤ a n := by
  if h : n = 3324 then
    subst h; exact five_le_a_3324
  else if h : n = 3330 then
    subst h; exact five_le_a_3330
  else if h : n = 3336 then
    subst h; exact five_le_a_3336
  else if h : n = 3342 then
    subst h; exact five_le_a_3342
  else if h : n = 3348 then
    subst h; exact five_le_a_3348
  else if h : n = 3354 then
    subst h; exact five_le_a_3354
  else if h : n = 3360 then
    subst h; exact five_le_a_3360
  else if h : n = 3366 then
    subst h; exact five_le_a_3366
  else if h : n = 3372 then
    subst h; exact five_le_a_3372
  else if h : n = 3378 then
    subst h; exact five_le_a_3378
  else if h : n = 3384 then
    subst h; exact five_le_a_3384
  else if h : n = 3390 then
    subst h; exact five_le_a_3390
  else if h : n = 3396 then
    subst h; exact five_le_a_3396
  else if h : n = 3402 then
    subst h; exact five_le_a_3402
  else if h : n = 3408 then
    subst h; exact five_le_a_3408
  else if h : n = 3414 then
    subst h; exact five_le_a_3414
  else if h : n = 3420 then
    subst h; exact five_le_a_3420
  else if h : n = 3426 then
    subst h; exact five_le_a_3426
  else if h : n = 3432 then
    subst h; exact five_le_a_3432
  else if h : n = 3438 then
    subst h; exact five_le_a_3438
  else if h : n = 3444 then
    subst h; exact five_le_a_3444
  else if h : n = 3450 then
    subst h; exact five_le_a_3450
  else if h : n = 3456 then
    subst h; exact five_le_a_3456
  else if h : n = 3462 then
    subst h; exact five_le_a_3462
  else if h : n = 3468 then
    subst h; exact five_le_a_3468
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_23 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3474 ≤ n) (hle : n ≤ 3618) : 5 ≤ a n := by
  if h : n = 3474 then
    subst h; exact five_le_a_3474
  else if h : n = 3480 then
    subst h; exact five_le_a_3480
  else if h : n = 3486 then
    subst h; exact five_le_a_3486
  else if h : n = 3492 then
    subst h; exact five_le_a_3492
  else if h : n = 3498 then
    subst h; exact five_le_a_3498
  else if h : n = 3504 then
    subst h; exact five_le_a_3504
  else if h : n = 3510 then
    subst h; exact five_le_a_3510
  else if h : n = 3516 then
    subst h; exact five_le_a_3516
  else if h : n = 3522 then
    subst h; exact five_le_a_3522
  else if h : n = 3528 then
    subst h; exact five_le_a_3528
  else if h : n = 3534 then
    subst h; exact five_le_a_3534
  else if h : n = 3540 then
    subst h; exact five_le_a_3540
  else if h : n = 3546 then
    subst h; exact five_le_a_3546
  else if h : n = 3552 then
    subst h; exact five_le_a_3552
  else if h : n = 3558 then
    subst h; exact five_le_a_3558
  else if h : n = 3564 then
    subst h; exact five_le_a_3564
  else if h : n = 3570 then
    subst h; exact five_le_a_3570
  else if h : n = 3576 then
    subst h; exact five_le_a_3576
  else if h : n = 3582 then
    subst h; exact five_le_a_3582
  else if h : n = 3588 then
    subst h; exact five_le_a_3588
  else if h : n = 3594 then
    subst h; exact five_le_a_3594
  else if h : n = 3600 then
    subst h; exact five_le_a_3600
  else if h : n = 3606 then
    subst h; exact five_le_a_3606
  else if h : n = 3612 then
    subst h; exact five_le_a_3612
  else if h : n = 3618 then
    subst h; exact five_le_a_3618
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_24 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3624 ≤ n) (hle : n ≤ 3768) : 5 ≤ a n := by
  if h : n = 3624 then
    subst h; exact five_le_a_3624
  else if h : n = 3630 then
    subst h; exact five_le_a_3630
  else if h : n = 3636 then
    subst h; exact five_le_a_3636
  else if h : n = 3642 then
    subst h; exact five_le_a_3642
  else if h : n = 3648 then
    subst h; exact five_le_a_3648
  else if h : n = 3654 then
    subst h; exact five_le_a_3654
  else if h : n = 3660 then
    subst h; exact five_le_a_3660
  else if h : n = 3666 then
    subst h; exact five_le_a_3666
  else if h : n = 3672 then
    subst h; exact five_le_a_3672
  else if h : n = 3678 then
    subst h; exact five_le_a_3678
  else if h : n = 3684 then
    subst h; exact five_le_a_3684
  else if h : n = 3690 then
    subst h; exact five_le_a_3690
  else if h : n = 3696 then
    subst h; exact five_le_a_3696
  else if h : n = 3702 then
    subst h; exact five_le_a_3702
  else if h : n = 3708 then
    subst h; exact five_le_a_3708
  else if h : n = 3714 then
    subst h; exact five_le_a_3714
  else if h : n = 3720 then
    subst h; exact five_le_a_3720
  else if h : n = 3726 then
    subst h; exact five_le_a_3726
  else if h : n = 3732 then
    subst h; exact five_le_a_3732
  else if h : n = 3738 then
    subst h; exact five_le_a_3738
  else if h : n = 3744 then
    subst h; exact five_le_a_3744
  else if h : n = 3750 then
    subst h; exact five_le_a_3750
  else if h : n = 3756 then
    subst h; exact five_le_a_3756
  else if h : n = 3762 then
    subst h; exact five_le_a_3762
  else if h : n = 3768 then
    subst h; exact five_le_a_3768
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_25 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3774 ≤ n) (hle : n ≤ 3918) : 5 ≤ a n := by
  if h : n = 3774 then
    subst h; exact five_le_a_3774
  else if h : n = 3780 then
    subst h; exact five_le_a_3780
  else if h : n = 3786 then
    subst h; exact five_le_a_3786
  else if h : n = 3792 then
    subst h; exact five_le_a_3792
  else if h : n = 3798 then
    subst h; exact five_le_a_3798
  else if h : n = 3804 then
    subst h; exact five_le_a_3804
  else if h : n = 3810 then
    subst h; exact five_le_a_3810
  else if h : n = 3816 then
    subst h; exact five_le_a_3816
  else if h : n = 3822 then
    subst h; exact five_le_a_3822
  else if h : n = 3828 then
    subst h; exact five_le_a_3828
  else if h : n = 3834 then
    subst h; exact five_le_a_3834
  else if h : n = 3840 then
    subst h; exact five_le_a_3840
  else if h : n = 3846 then
    subst h; exact five_le_a_3846
  else if h : n = 3852 then
    subst h; exact five_le_a_3852
  else if h : n = 3858 then
    subst h; exact five_le_a_3858
  else if h : n = 3864 then
    subst h; exact five_le_a_3864
  else if h : n = 3870 then
    subst h; exact five_le_a_3870
  else if h : n = 3876 then
    subst h; exact five_le_a_3876
  else if h : n = 3882 then
    subst h; exact five_le_a_3882
  else if h : n = 3888 then
    subst h; exact five_le_a_3888
  else if h : n = 3894 then
    subst h; exact five_le_a_3894
  else if h : n = 3900 then
    subst h; exact five_le_a_3900
  else if h : n = 3906 then
    subst h; exact five_le_a_3906
  else if h : n = 3912 then
    subst h; exact five_le_a_3912
  else if h : n = 3918 then
    subst h; exact five_le_a_3918
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_26 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 3924 ≤ n) (hle : n ≤ 4068) : 5 ≤ a n := by
  if h : n = 3924 then
    subst h; exact five_le_a_3924
  else if h : n = 3930 then
    subst h; exact five_le_a_3930
  else if h : n = 3936 then
    subst h; exact five_le_a_3936
  else if h : n = 3942 then
    subst h; exact five_le_a_3942
  else if h : n = 3948 then
    subst h; exact five_le_a_3948
  else if h : n = 3954 then
    subst h; exact five_le_a_3954
  else if h : n = 3960 then
    subst h; exact five_le_a_3960
  else if h : n = 3966 then
    subst h; exact five_le_a_3966
  else if h : n = 3972 then
    subst h; exact five_le_a_3972
  else if h : n = 3978 then
    subst h; exact five_le_a_3978
  else if h : n = 3984 then
    subst h; exact five_le_a_3984
  else if h : n = 3990 then
    subst h; exact five_le_a_3990
  else if h : n = 3996 then
    subst h; exact five_le_a_3996
  else if h : n = 4002 then
    subst h; exact five_le_a_4002
  else if h : n = 4008 then
    subst h; exact five_le_a_4008
  else if h : n = 4014 then
    subst h; exact five_le_a_4014
  else if h : n = 4020 then
    subst h; exact five_le_a_4020
  else if h : n = 4026 then
    subst h; exact five_le_a_4026
  else if h : n = 4032 then
    subst h; exact five_le_a_4032
  else if h : n = 4038 then
    subst h; exact five_le_a_4038
  else if h : n = 4044 then
    subst h; exact five_le_a_4044
  else if h : n = 4050 then
    subst h; exact five_le_a_4050
  else if h : n = 4056 then
    subst h; exact five_le_a_4056
  else if h : n = 4062 then
    subst h; exact five_le_a_4062
  else if h : n = 4068 then
    subst h; exact five_le_a_4068
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_27 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4074 ≤ n) (hle : n ≤ 4218) : 5 ≤ a n := by
  if h : n = 4074 then
    subst h; exact five_le_a_4074
  else if h : n = 4080 then
    subst h; exact five_le_a_4080
  else if h : n = 4086 then
    subst h; exact five_le_a_4086
  else if h : n = 4092 then
    subst h; exact five_le_a_4092
  else if h : n = 4098 then
    subst h; exact five_le_a_4098
  else if h : n = 4104 then
    subst h; exact five_le_a_4104
  else if h : n = 4110 then
    subst h; exact five_le_a_4110
  else if h : n = 4116 then
    subst h; exact five_le_a_4116
  else if h : n = 4122 then
    subst h; exact five_le_a_4122
  else if h : n = 4128 then
    subst h; exact five_le_a_4128
  else if h : n = 4134 then
    subst h; exact five_le_a_4134
  else if h : n = 4140 then
    subst h; exact five_le_a_4140
  else if h : n = 4146 then
    subst h; exact five_le_a_4146
  else if h : n = 4152 then
    subst h; exact five_le_a_4152
  else if h : n = 4158 then
    subst h; exact five_le_a_4158
  else if h : n = 4164 then
    subst h; exact five_le_a_4164
  else if h : n = 4170 then
    subst h; exact five_le_a_4170
  else if h : n = 4176 then
    subst h; exact five_le_a_4176
  else if h : n = 4182 then
    subst h; exact five_le_a_4182
  else if h : n = 4188 then
    subst h; exact five_le_a_4188
  else if h : n = 4194 then
    subst h; exact five_le_a_4194
  else if h : n = 4200 then
    subst h; exact five_le_a_4200
  else if h : n = 4206 then
    subst h; exact five_le_a_4206
  else if h : n = 4212 then
    subst h; exact five_le_a_4212
  else if h : n = 4218 then
    subst h; exact five_le_a_4218
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_28 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4224 ≤ n) (hle : n ≤ 4368) : 5 ≤ a n := by
  if h : n = 4224 then
    subst h; exact five_le_a_4224
  else if h : n = 4230 then
    subst h; exact five_le_a_4230
  else if h : n = 4236 then
    subst h; exact five_le_a_4236
  else if h : n = 4242 then
    subst h; exact five_le_a_4242
  else if h : n = 4248 then
    subst h; exact five_le_a_4248
  else if h : n = 4254 then
    subst h; exact five_le_a_4254
  else if h : n = 4260 then
    subst h; exact five_le_a_4260
  else if h : n = 4266 then
    subst h; exact five_le_a_4266
  else if h : n = 4272 then
    subst h; exact five_le_a_4272
  else if h : n = 4278 then
    subst h; exact five_le_a_4278
  else if h : n = 4284 then
    subst h; exact five_le_a_4284
  else if h : n = 4290 then
    subst h; exact five_le_a_4290
  else if h : n = 4296 then
    subst h; exact five_le_a_4296
  else if h : n = 4302 then
    subst h; exact five_le_a_4302
  else if h : n = 4308 then
    subst h; exact five_le_a_4308
  else if h : n = 4314 then
    subst h; exact five_le_a_4314
  else if h : n = 4320 then
    subst h; exact five_le_a_4320
  else if h : n = 4326 then
    subst h; exact five_le_a_4326
  else if h : n = 4332 then
    subst h; exact five_le_a_4332
  else if h : n = 4338 then
    subst h; exact five_le_a_4338
  else if h : n = 4344 then
    subst h; exact five_le_a_4344
  else if h : n = 4350 then
    subst h; exact five_le_a_4350
  else if h : n = 4356 then
    subst h; exact five_le_a_4356
  else if h : n = 4362 then
    subst h; exact five_le_a_4362
  else if h : n = 4368 then
    subst h; exact five_le_a_4368
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_29 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4374 ≤ n) (hle : n ≤ 4518) : 5 ≤ a n := by
  if h : n = 4374 then
    subst h; exact five_le_a_4374
  else if h : n = 4380 then
    subst h; exact five_le_a_4380
  else if h : n = 4386 then
    subst h; exact five_le_a_4386
  else if h : n = 4392 then
    subst h; exact five_le_a_4392
  else if h : n = 4398 then
    subst h; exact five_le_a_4398
  else if h : n = 4404 then
    subst h; exact five_le_a_4404
  else if h : n = 4410 then
    subst h; exact five_le_a_4410
  else if h : n = 4416 then
    subst h; exact five_le_a_4416
  else if h : n = 4422 then
    subst h; exact five_le_a_4422
  else if h : n = 4428 then
    subst h; exact five_le_a_4428
  else if h : n = 4434 then
    subst h; exact five_le_a_4434
  else if h : n = 4440 then
    subst h; exact five_le_a_4440
  else if h : n = 4446 then
    subst h; exact five_le_a_4446
  else if h : n = 4452 then
    subst h; exact five_le_a_4452
  else if h : n = 4458 then
    subst h; exact five_le_a_4458
  else if h : n = 4464 then
    subst h; exact five_le_a_4464
  else if h : n = 4470 then
    subst h; exact five_le_a_4470
  else if h : n = 4476 then
    subst h; exact five_le_a_4476
  else if h : n = 4482 then
    subst h; exact five_le_a_4482
  else if h : n = 4488 then
    subst h; exact five_le_a_4488
  else if h : n = 4494 then
    subst h; exact five_le_a_4494
  else if h : n = 4500 then
    subst h; exact five_le_a_4500
  else if h : n = 4506 then
    subst h; exact five_le_a_4506
  else if h : n = 4512 then
    subst h; exact five_le_a_4512
  else if h : n = 4518 then
    subst h; exact five_le_a_4518
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_30 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4524 ≤ n) (hle : n ≤ 4668) : 5 ≤ a n := by
  if h : n = 4524 then
    subst h; exact five_le_a_4524
  else if h : n = 4530 then
    subst h; exact five_le_a_4530
  else if h : n = 4536 then
    subst h; exact five_le_a_4536
  else if h : n = 4542 then
    subst h; exact five_le_a_4542
  else if h : n = 4548 then
    subst h; exact five_le_a_4548
  else if h : n = 4554 then
    subst h; exact five_le_a_4554
  else if h : n = 4560 then
    subst h; exact five_le_a_4560
  else if h : n = 4566 then
    subst h; exact five_le_a_4566
  else if h : n = 4572 then
    subst h; exact five_le_a_4572
  else if h : n = 4578 then
    subst h; exact five_le_a_4578
  else if h : n = 4584 then
    subst h; exact five_le_a_4584
  else if h : n = 4590 then
    subst h; exact five_le_a_4590
  else if h : n = 4596 then
    subst h; exact five_le_a_4596
  else if h : n = 4602 then
    subst h; exact five_le_a_4602
  else if h : n = 4608 then
    subst h; exact five_le_a_4608
  else if h : n = 4614 then
    subst h; exact five_le_a_4614
  else if h : n = 4620 then
    subst h; exact five_le_a_4620
  else if h : n = 4626 then
    subst h; exact five_le_a_4626
  else if h : n = 4632 then
    subst h; exact five_le_a_4632
  else if h : n = 4638 then
    subst h; exact five_le_a_4638
  else if h : n = 4644 then
    subst h; exact five_le_a_4644
  else if h : n = 4650 then
    subst h; exact five_le_a_4650
  else if h : n = 4656 then
    subst h; exact five_le_a_4656
  else if h : n = 4662 then
    subst h; exact five_le_a_4662
  else if h : n = 4668 then
    subst h; exact five_le_a_4668
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_31 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4674 ≤ n) (hle : n ≤ 4818) : 5 ≤ a n := by
  if h : n = 4674 then
    subst h; exact five_le_a_4674
  else if h : n = 4680 then
    subst h; exact five_le_a_4680
  else if h : n = 4686 then
    subst h; exact five_le_a_4686
  else if h : n = 4692 then
    subst h; exact five_le_a_4692
  else if h : n = 4698 then
    subst h; exact five_le_a_4698
  else if h : n = 4704 then
    subst h; exact five_le_a_4704
  else if h : n = 4710 then
    subst h; exact five_le_a_4710
  else if h : n = 4716 then
    subst h; exact five_le_a_4716
  else if h : n = 4722 then
    subst h; exact five_le_a_4722
  else if h : n = 4728 then
    subst h; exact five_le_a_4728
  else if h : n = 4734 then
    subst h; exact five_le_a_4734
  else if h : n = 4740 then
    subst h; exact five_le_a_4740
  else if h : n = 4746 then
    subst h; exact five_le_a_4746
  else if h : n = 4752 then
    subst h; exact five_le_a_4752
  else if h : n = 4758 then
    subst h; exact five_le_a_4758
  else if h : n = 4764 then
    subst h; exact five_le_a_4764
  else if h : n = 4770 then
    subst h; exact five_le_a_4770
  else if h : n = 4776 then
    subst h; exact five_le_a_4776
  else if h : n = 4782 then
    subst h; exact five_le_a_4782
  else if h : n = 4788 then
    subst h; exact five_le_a_4788
  else if h : n = 4794 then
    subst h; exact five_le_a_4794
  else if h : n = 4800 then
    subst h; exact five_le_a_4800
  else if h : n = 4806 then
    subst h; exact five_le_a_4806
  else if h : n = 4812 then
    subst h; exact five_le_a_4812
  else if h : n = 4818 then
    subst h; exact five_le_a_4818
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_32 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4824 ≤ n) (hle : n ≤ 4968) : 5 ≤ a n := by
  if h : n = 4824 then
    subst h; exact five_le_a_4824
  else if h : n = 4830 then
    subst h; exact five_le_a_4830
  else if h : n = 4836 then
    subst h; exact five_le_a_4836
  else if h : n = 4842 then
    subst h; exact five_le_a_4842
  else if h : n = 4848 then
    subst h; exact five_le_a_4848
  else if h : n = 4854 then
    subst h; exact five_le_a_4854
  else if h : n = 4860 then
    subst h; exact five_le_a_4860
  else if h : n = 4866 then
    subst h; exact five_le_a_4866
  else if h : n = 4872 then
    subst h; exact five_le_a_4872
  else if h : n = 4878 then
    subst h; exact five_le_a_4878
  else if h : n = 4884 then
    subst h; exact five_le_a_4884
  else if h : n = 4890 then
    subst h; exact five_le_a_4890
  else if h : n = 4896 then
    subst h; exact five_le_a_4896
  else if h : n = 4902 then
    subst h; exact five_le_a_4902
  else if h : n = 4908 then
    subst h; exact five_le_a_4908
  else if h : n = 4914 then
    subst h; exact five_le_a_4914
  else if h : n = 4920 then
    subst h; exact five_le_a_4920
  else if h : n = 4926 then
    subst h; exact five_le_a_4926
  else if h : n = 4932 then
    subst h; exact five_le_a_4932
  else if h : n = 4938 then
    subst h; exact five_le_a_4938
  else if h : n = 4944 then
    subst h; exact five_le_a_4944
  else if h : n = 4950 then
    subst h; exact five_le_a_4950
  else if h : n = 4956 then
    subst h; exact five_le_a_4956
  else if h : n = 4962 then
    subst h; exact five_le_a_4962
  else if h : n = 4968 then
    subst h; exact five_le_a_4968
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_33 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 4974 ≤ n) (hle : n ≤ 5118) : 5 ≤ a n := by
  if h : n = 4974 then
    subst h; exact five_le_a_4974
  else if h : n = 4980 then
    subst h; exact five_le_a_4980
  else if h : n = 4986 then
    subst h; exact five_le_a_4986
  else if h : n = 4992 then
    subst h; exact five_le_a_4992
  else if h : n = 4998 then
    subst h; exact five_le_a_4998
  else if h : n = 5004 then
    subst h; exact five_le_a_5004
  else if h : n = 5010 then
    subst h; exact five_le_a_5010
  else if h : n = 5016 then
    subst h; exact five_le_a_5016
  else if h : n = 5022 then
    subst h; exact five_le_a_5022
  else if h : n = 5028 then
    subst h; exact five_le_a_5028
  else if h : n = 5034 then
    subst h; exact five_le_a_5034
  else if h : n = 5040 then
    subst h; exact five_le_a_5040
  else if h : n = 5046 then
    subst h; exact five_le_a_5046
  else if h : n = 5052 then
    subst h; exact five_le_a_5052
  else if h : n = 5058 then
    subst h; exact five_le_a_5058
  else if h : n = 5064 then
    subst h; exact five_le_a_5064
  else if h : n = 5070 then
    subst h; exact five_le_a_5070
  else if h : n = 5076 then
    subst h; exact five_le_a_5076
  else if h : n = 5082 then
    subst h; exact five_le_a_5082
  else if h : n = 5088 then
    subst h; exact five_le_a_5088
  else if h : n = 5094 then
    subst h; exact five_le_a_5094
  else if h : n = 5100 then
    subst h; exact five_le_a_5100
  else if h : n = 5106 then
    subst h; exact five_le_a_5106
  else if h : n = 5112 then
    subst h; exact five_le_a_5112
  else if h : n = 5118 then
    subst h; exact five_le_a_5118
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_34 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5124 ≤ n) (hle : n ≤ 5268) : 5 ≤ a n := by
  if h : n = 5124 then
    subst h; exact five_le_a_5124
  else if h : n = 5130 then
    subst h; exact five_le_a_5130
  else if h : n = 5136 then
    subst h; exact five_le_a_5136
  else if h : n = 5142 then
    subst h; exact five_le_a_5142
  else if h : n = 5148 then
    subst h; exact five_le_a_5148
  else if h : n = 5154 then
    subst h; exact five_le_a_5154
  else if h : n = 5160 then
    subst h; exact five_le_a_5160
  else if h : n = 5166 then
    subst h; exact five_le_a_5166
  else if h : n = 5172 then
    subst h; exact five_le_a_5172
  else if h : n = 5178 then
    subst h; exact five_le_a_5178
  else if h : n = 5184 then
    subst h; exact five_le_a_5184
  else if h : n = 5190 then
    subst h; exact five_le_a_5190
  else if h : n = 5196 then
    subst h; exact five_le_a_5196
  else if h : n = 5202 then
    subst h; exact five_le_a_5202
  else if h : n = 5208 then
    subst h; exact five_le_a_5208
  else if h : n = 5214 then
    subst h; exact five_le_a_5214
  else if h : n = 5220 then
    subst h; exact five_le_a_5220
  else if h : n = 5226 then
    subst h; exact five_le_a_5226
  else if h : n = 5232 then
    subst h; exact five_le_a_5232
  else if h : n = 5238 then
    subst h; exact five_le_a_5238
  else if h : n = 5244 then
    subst h; exact five_le_a_5244
  else if h : n = 5250 then
    subst h; exact five_le_a_5250
  else if h : n = 5256 then
    subst h; exact five_le_a_5256
  else if h : n = 5262 then
    subst h; exact five_le_a_5262
  else if h : n = 5268 then
    subst h; exact five_le_a_5268
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_35 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5274 ≤ n) (hle : n ≤ 5418) : 5 ≤ a n := by
  if h : n = 5274 then
    subst h; exact five_le_a_5274
  else if h : n = 5280 then
    subst h; exact five_le_a_5280
  else if h : n = 5286 then
    subst h; exact five_le_a_5286
  else if h : n = 5292 then
    subst h; exact five_le_a_5292
  else if h : n = 5298 then
    subst h; exact five_le_a_5298
  else if h : n = 5304 then
    subst h; exact five_le_a_5304
  else if h : n = 5310 then
    subst h; exact five_le_a_5310
  else if h : n = 5316 then
    subst h; exact five_le_a_5316
  else if h : n = 5322 then
    subst h; exact five_le_a_5322
  else if h : n = 5328 then
    subst h; exact five_le_a_5328
  else if h : n = 5334 then
    subst h; exact five_le_a_5334
  else if h : n = 5340 then
    subst h; exact five_le_a_5340
  else if h : n = 5346 then
    subst h; exact five_le_a_5346
  else if h : n = 5352 then
    subst h; exact five_le_a_5352
  else if h : n = 5358 then
    subst h; exact five_le_a_5358
  else if h : n = 5364 then
    subst h; exact five_le_a_5364
  else if h : n = 5370 then
    subst h; exact five_le_a_5370
  else if h : n = 5376 then
    subst h; exact five_le_a_5376
  else if h : n = 5382 then
    subst h; exact five_le_a_5382
  else if h : n = 5388 then
    subst h; exact five_le_a_5388
  else if h : n = 5394 then
    subst h; exact five_le_a_5394
  else if h : n = 5400 then
    subst h; exact five_le_a_5400
  else if h : n = 5406 then
    subst h; exact five_le_a_5406
  else if h : n = 5412 then
    subst h; exact five_le_a_5412
  else if h : n = 5418 then
    subst h; exact five_le_a_5418
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_36 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5424 ≤ n) (hle : n ≤ 5568) : 5 ≤ a n := by
  if h : n = 5424 then
    subst h; exact five_le_a_5424
  else if h : n = 5430 then
    subst h; exact five_le_a_5430
  else if h : n = 5436 then
    subst h; exact five_le_a_5436
  else if h : n = 5442 then
    subst h; exact five_le_a_5442
  else if h : n = 5448 then
    subst h; exact five_le_a_5448
  else if h : n = 5454 then
    subst h; exact five_le_a_5454
  else if h : n = 5460 then
    subst h; exact five_le_a_5460
  else if h : n = 5466 then
    subst h; exact five_le_a_5466
  else if h : n = 5472 then
    subst h; exact five_le_a_5472
  else if h : n = 5478 then
    subst h; exact five_le_a_5478
  else if h : n = 5484 then
    subst h; exact five_le_a_5484
  else if h : n = 5490 then
    subst h; exact five_le_a_5490
  else if h : n = 5496 then
    subst h; exact five_le_a_5496
  else if h : n = 5502 then
    subst h; exact five_le_a_5502
  else if h : n = 5508 then
    subst h; exact five_le_a_5508
  else if h : n = 5514 then
    subst h; exact five_le_a_5514
  else if h : n = 5520 then
    subst h; exact five_le_a_5520
  else if h : n = 5526 then
    subst h; exact five_le_a_5526
  else if h : n = 5532 then
    subst h; exact five_le_a_5532
  else if h : n = 5538 then
    subst h; exact five_le_a_5538
  else if h : n = 5544 then
    subst h; exact five_le_a_5544
  else if h : n = 5550 then
    subst h; exact five_le_a_5550
  else if h : n = 5556 then
    subst h; exact five_le_a_5556
  else if h : n = 5562 then
    subst h; exact five_le_a_5562
  else if h : n = 5568 then
    subst h; exact five_le_a_5568
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_37 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5574 ≤ n) (hle : n ≤ 5718) : 5 ≤ a n := by
  if h : n = 5574 then
    subst h; exact five_le_a_5574
  else if h : n = 5580 then
    subst h; exact five_le_a_5580
  else if h : n = 5586 then
    subst h; exact five_le_a_5586
  else if h : n = 5592 then
    subst h; exact five_le_a_5592
  else if h : n = 5598 then
    subst h; exact five_le_a_5598
  else if h : n = 5604 then
    subst h; exact five_le_a_5604
  else if h : n = 5610 then
    subst h; exact five_le_a_5610
  else if h : n = 5616 then
    subst h; exact five_le_a_5616
  else if h : n = 5622 then
    subst h; exact five_le_a_5622
  else if h : n = 5628 then
    subst h; exact five_le_a_5628
  else if h : n = 5634 then
    subst h; exact five_le_a_5634
  else if h : n = 5640 then
    subst h; exact five_le_a_5640
  else if h : n = 5646 then
    subst h; exact five_le_a_5646
  else if h : n = 5652 then
    subst h; exact five_le_a_5652
  else if h : n = 5658 then
    subst h; exact five_le_a_5658
  else if h : n = 5664 then
    subst h; exact five_le_a_5664
  else if h : n = 5670 then
    subst h; exact five_le_a_5670
  else if h : n = 5676 then
    subst h; exact five_le_a_5676
  else if h : n = 5682 then
    subst h; exact five_le_a_5682
  else if h : n = 5688 then
    subst h; exact five_le_a_5688
  else if h : n = 5694 then
    subst h; exact five_le_a_5694
  else if h : n = 5700 then
    subst h; exact five_le_a_5700
  else if h : n = 5706 then
    subst h; exact five_le_a_5706
  else if h : n = 5712 then
    subst h; exact five_le_a_5712
  else if h : n = 5718 then
    subst h; exact five_le_a_5718
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_38 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5724 ≤ n) (hle : n ≤ 5868) : 5 ≤ a n := by
  if h : n = 5724 then
    subst h; exact five_le_a_5724
  else if h : n = 5730 then
    subst h; exact five_le_a_5730
  else if h : n = 5736 then
    subst h; exact five_le_a_5736
  else if h : n = 5742 then
    subst h; exact five_le_a_5742
  else if h : n = 5748 then
    subst h; exact five_le_a_5748
  else if h : n = 5754 then
    subst h; exact five_le_a_5754
  else if h : n = 5760 then
    subst h; exact five_le_a_5760
  else if h : n = 5766 then
    subst h; exact five_le_a_5766
  else if h : n = 5772 then
    subst h; exact five_le_a_5772
  else if h : n = 5778 then
    subst h; exact five_le_a_5778
  else if h : n = 5784 then
    subst h; exact five_le_a_5784
  else if h : n = 5790 then
    subst h; exact five_le_a_5790
  else if h : n = 5796 then
    subst h; exact five_le_a_5796
  else if h : n = 5802 then
    subst h; exact five_le_a_5802
  else if h : n = 5808 then
    subst h; exact five_le_a_5808
  else if h : n = 5814 then
    subst h; exact five_le_a_5814
  else if h : n = 5820 then
    subst h; exact five_le_a_5820
  else if h : n = 5826 then
    subst h; exact five_le_a_5826
  else if h : n = 5832 then
    subst h; exact five_le_a_5832
  else if h : n = 5838 then
    subst h; exact five_le_a_5838
  else if h : n = 5844 then
    subst h; exact five_le_a_5844
  else if h : n = 5850 then
    subst h; exact five_le_a_5850
  else if h : n = 5856 then
    subst h; exact five_le_a_5856
  else if h : n = 5862 then
    subst h; exact five_le_a_5862
  else if h : n = 5868 then
    subst h; exact five_le_a_5868
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_39 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 5874 ≤ n) (hle : n ≤ 6018) : 5 ≤ a n := by
  if h : n = 5874 then
    subst h; exact five_le_a_5874
  else if h : n = 5880 then
    subst h; exact five_le_a_5880
  else if h : n = 5886 then
    subst h; exact five_le_a_5886
  else if h : n = 5892 then
    subst h; exact five_le_a_5892
  else if h : n = 5898 then
    subst h; exact five_le_a_5898
  else if h : n = 5904 then
    subst h; exact five_le_a_5904
  else if h : n = 5910 then
    subst h; exact five_le_a_5910
  else if h : n = 5916 then
    subst h; exact five_le_a_5916
  else if h : n = 5922 then
    subst h; exact five_le_a_5922
  else if h : n = 5928 then
    subst h; exact five_le_a_5928
  else if h : n = 5934 then
    subst h; exact five_le_a_5934
  else if h : n = 5940 then
    subst h; exact five_le_a_5940
  else if h : n = 5946 then
    subst h; exact five_le_a_5946
  else if h : n = 5952 then
    subst h; exact five_le_a_5952
  else if h : n = 5958 then
    subst h; exact five_le_a_5958
  else if h : n = 5964 then
    subst h; exact five_le_a_5964
  else if h : n = 5970 then
    subst h; exact five_le_a_5970
  else if h : n = 5976 then
    subst h; exact five_le_a_5976
  else if h : n = 5982 then
    subst h; exact five_le_a_5982
  else if h : n = 5988 then
    subst h; exact five_le_a_5988
  else if h : n = 5994 then
    subst h; exact five_le_a_5994
  else if h : n = 6000 then
    subst h; exact five_le_a_6000
  else if h : n = 6006 then
    subst h; exact five_le_a_6006
  else if h : n = 6012 then
    subst h; exact five_le_a_6012
  else if h : n = 6018 then
    subst h; exact five_le_a_6018
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_40 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6024 ≤ n) (hle : n ≤ 6168) : 5 ≤ a n := by
  if h : n = 6024 then
    subst h; exact five_le_a_6024
  else if h : n = 6030 then
    subst h; exact five_le_a_6030
  else if h : n = 6036 then
    subst h; exact five_le_a_6036
  else if h : n = 6042 then
    subst h; exact five_le_a_6042
  else if h : n = 6048 then
    subst h; exact five_le_a_6048
  else if h : n = 6054 then
    subst h; exact five_le_a_6054
  else if h : n = 6060 then
    subst h; exact five_le_a_6060
  else if h : n = 6066 then
    subst h; exact five_le_a_6066
  else if h : n = 6072 then
    subst h; exact five_le_a_6072
  else if h : n = 6078 then
    subst h; exact five_le_a_6078
  else if h : n = 6084 then
    subst h; exact five_le_a_6084
  else if h : n = 6090 then
    subst h; exact five_le_a_6090
  else if h : n = 6096 then
    subst h; exact five_le_a_6096
  else if h : n = 6102 then
    subst h; exact five_le_a_6102
  else if h : n = 6108 then
    subst h; exact five_le_a_6108
  else if h : n = 6114 then
    subst h; exact five_le_a_6114
  else if h : n = 6120 then
    subst h; exact five_le_a_6120
  else if h : n = 6126 then
    subst h; exact five_le_a_6126
  else if h : n = 6132 then
    subst h; exact five_le_a_6132
  else if h : n = 6138 then
    subst h; exact five_le_a_6138
  else if h : n = 6144 then
    subst h; exact five_le_a_6144
  else if h : n = 6150 then
    subst h; exact five_le_a_6150
  else if h : n = 6156 then
    subst h; exact five_le_a_6156
  else if h : n = 6162 then
    subst h; exact five_le_a_6162
  else if h : n = 6168 then
    subst h; exact five_le_a_6168
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_41 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6174 ≤ n) (hle : n ≤ 6318) : 5 ≤ a n := by
  if h : n = 6174 then
    subst h; exact five_le_a_6174
  else if h : n = 6180 then
    subst h; exact five_le_a_6180
  else if h : n = 6186 then
    subst h; exact five_le_a_6186
  else if h : n = 6192 then
    subst h; exact five_le_a_6192
  else if h : n = 6198 then
    subst h; exact five_le_a_6198
  else if h : n = 6204 then
    subst h; exact five_le_a_6204
  else if h : n = 6210 then
    subst h; exact five_le_a_6210
  else if h : n = 6216 then
    subst h; exact five_le_a_6216
  else if h : n = 6222 then
    subst h; exact five_le_a_6222
  else if h : n = 6228 then
    subst h; exact five_le_a_6228
  else if h : n = 6234 then
    subst h; exact five_le_a_6234
  else if h : n = 6240 then
    subst h; exact five_le_a_6240
  else if h : n = 6246 then
    subst h; exact five_le_a_6246
  else if h : n = 6252 then
    subst h; exact five_le_a_6252
  else if h : n = 6258 then
    subst h; exact five_le_a_6258
  else if h : n = 6264 then
    subst h; exact five_le_a_6264
  else if h : n = 6270 then
    subst h; exact five_le_a_6270
  else if h : n = 6276 then
    subst h; exact five_le_a_6276
  else if h : n = 6282 then
    subst h; exact five_le_a_6282
  else if h : n = 6288 then
    subst h; exact five_le_a_6288
  else if h : n = 6294 then
    subst h; exact five_le_a_6294
  else if h : n = 6300 then
    subst h; exact five_le_a_6300
  else if h : n = 6306 then
    subst h; exact five_le_a_6306
  else if h : n = 6312 then
    subst h; exact five_le_a_6312
  else if h : n = 6318 then
    subst h; exact five_le_a_6318
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_42 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6324 ≤ n) (hle : n ≤ 6468) : 5 ≤ a n := by
  if h : n = 6324 then
    subst h; exact five_le_a_6324
  else if h : n = 6330 then
    subst h; exact five_le_a_6330
  else if h : n = 6336 then
    subst h; exact five_le_a_6336
  else if h : n = 6342 then
    subst h; exact five_le_a_6342
  else if h : n = 6348 then
    subst h; exact five_le_a_6348
  else if h : n = 6354 then
    subst h; exact five_le_a_6354
  else if h : n = 6360 then
    subst h; exact five_le_a_6360
  else if h : n = 6366 then
    subst h; exact five_le_a_6366
  else if h : n = 6372 then
    subst h; exact five_le_a_6372
  else if h : n = 6378 then
    subst h; exact five_le_a_6378
  else if h : n = 6384 then
    subst h; exact five_le_a_6384
  else if h : n = 6390 then
    subst h; exact five_le_a_6390
  else if h : n = 6396 then
    subst h; exact five_le_a_6396
  else if h : n = 6402 then
    subst h; exact five_le_a_6402
  else if h : n = 6408 then
    subst h; exact five_le_a_6408
  else if h : n = 6414 then
    subst h; exact five_le_a_6414
  else if h : n = 6420 then
    subst h; exact five_le_a_6420
  else if h : n = 6426 then
    subst h; exact five_le_a_6426
  else if h : n = 6432 then
    subst h; exact five_le_a_6432
  else if h : n = 6438 then
    subst h; exact five_le_a_6438
  else if h : n = 6444 then
    subst h; exact five_le_a_6444
  else if h : n = 6450 then
    subst h; exact five_le_a_6450
  else if h : n = 6456 then
    subst h; exact five_le_a_6456
  else if h : n = 6462 then
    subst h; exact five_le_a_6462
  else if h : n = 6468 then
    subst h; exact five_le_a_6468
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_43 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6474 ≤ n) (hle : n ≤ 6618) : 5 ≤ a n := by
  if h : n = 6474 then
    subst h; exact five_le_a_6474
  else if h : n = 6480 then
    subst h; exact five_le_a_6480
  else if h : n = 6486 then
    subst h; exact five_le_a_6486
  else if h : n = 6492 then
    subst h; exact five_le_a_6492
  else if h : n = 6498 then
    subst h; exact five_le_a_6498
  else if h : n = 6504 then
    subst h; exact five_le_a_6504
  else if h : n = 6510 then
    subst h; exact five_le_a_6510
  else if h : n = 6516 then
    subst h; exact five_le_a_6516
  else if h : n = 6522 then
    subst h; exact five_le_a_6522
  else if h : n = 6528 then
    subst h; exact five_le_a_6528
  else if h : n = 6534 then
    subst h; exact five_le_a_6534
  else if h : n = 6540 then
    subst h; exact five_le_a_6540
  else if h : n = 6546 then
    subst h; exact five_le_a_6546
  else if h : n = 6552 then
    subst h; exact five_le_a_6552
  else if h : n = 6558 then
    subst h; exact five_le_a_6558
  else if h : n = 6564 then
    subst h; exact five_le_a_6564
  else if h : n = 6570 then
    subst h; exact five_le_a_6570
  else if h : n = 6576 then
    subst h; exact five_le_a_6576
  else if h : n = 6582 then
    subst h; exact five_le_a_6582
  else if h : n = 6588 then
    subst h; exact five_le_a_6588
  else if h : n = 6594 then
    subst h; exact five_le_a_6594
  else if h : n = 6600 then
    subst h; exact five_le_a_6600
  else if h : n = 6606 then
    subst h; exact five_le_a_6606
  else if h : n = 6612 then
    subst h; exact five_le_a_6612
  else if h : n = 6618 then
    subst h; exact five_le_a_6618
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_44 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6624 ≤ n) (hle : n ≤ 6768) : 5 ≤ a n := by
  if h : n = 6624 then
    subst h; exact five_le_a_6624
  else if h : n = 6630 then
    subst h; exact five_le_a_6630
  else if h : n = 6636 then
    subst h; exact five_le_a_6636
  else if h : n = 6642 then
    subst h; exact five_le_a_6642
  else if h : n = 6648 then
    subst h; exact five_le_a_6648
  else if h : n = 6654 then
    subst h; exact five_le_a_6654
  else if h : n = 6660 then
    subst h; exact five_le_a_6660
  else if h : n = 6666 then
    subst h; exact five_le_a_6666
  else if h : n = 6672 then
    subst h; exact five_le_a_6672
  else if h : n = 6678 then
    subst h; exact five_le_a_6678
  else if h : n = 6684 then
    subst h; exact five_le_a_6684
  else if h : n = 6690 then
    subst h; exact five_le_a_6690
  else if h : n = 6696 then
    subst h; exact five_le_a_6696
  else if h : n = 6702 then
    subst h; exact five_le_a_6702
  else if h : n = 6708 then
    subst h; exact five_le_a_6708
  else if h : n = 6714 then
    subst h; exact five_le_a_6714
  else if h : n = 6720 then
    subst h; exact five_le_a_6720
  else if h : n = 6726 then
    subst h; exact five_le_a_6726
  else if h : n = 6732 then
    subst h; exact five_le_a_6732
  else if h : n = 6738 then
    subst h; exact five_le_a_6738
  else if h : n = 6744 then
    subst h; exact five_le_a_6744
  else if h : n = 6750 then
    subst h; exact five_le_a_6750
  else if h : n = 6756 then
    subst h; exact five_le_a_6756
  else if h : n = 6762 then
    subst h; exact five_le_a_6762
  else if h : n = 6768 then
    subst h; exact five_le_a_6768
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_45 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6774 ≤ n) (hle : n ≤ 6918) : 5 ≤ a n := by
  if h : n = 6774 then
    subst h; exact five_le_a_6774
  else if h : n = 6780 then
    subst h; exact five_le_a_6780
  else if h : n = 6786 then
    subst h; exact five_le_a_6786
  else if h : n = 6792 then
    subst h; exact five_le_a_6792
  else if h : n = 6798 then
    subst h; exact five_le_a_6798
  else if h : n = 6804 then
    subst h; exact five_le_a_6804
  else if h : n = 6810 then
    subst h; exact five_le_a_6810
  else if h : n = 6816 then
    subst h; exact five_le_a_6816
  else if h : n = 6822 then
    subst h; exact five_le_a_6822
  else if h : n = 6828 then
    subst h; exact five_le_a_6828
  else if h : n = 6834 then
    subst h; exact five_le_a_6834
  else if h : n = 6840 then
    subst h; exact five_le_a_6840
  else if h : n = 6846 then
    subst h; exact five_le_a_6846
  else if h : n = 6852 then
    subst h; exact five_le_a_6852
  else if h : n = 6858 then
    subst h; exact five_le_a_6858
  else if h : n = 6864 then
    subst h; exact five_le_a_6864
  else if h : n = 6870 then
    subst h; exact five_le_a_6870
  else if h : n = 6876 then
    subst h; exact five_le_a_6876
  else if h : n = 6882 then
    subst h; exact five_le_a_6882
  else if h : n = 6888 then
    subst h; exact five_le_a_6888
  else if h : n = 6894 then
    subst h; exact five_le_a_6894
  else if h : n = 6900 then
    subst h; exact five_le_a_6900
  else if h : n = 6906 then
    subst h; exact five_le_a_6906
  else if h : n = 6912 then
    subst h; exact five_le_a_6912
  else if h : n = 6918 then
    subst h; exact five_le_a_6918
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_46 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 6924 ≤ n) (hle : n ≤ 7068) : 5 ≤ a n := by
  if h : n = 6924 then
    subst h; exact five_le_a_6924
  else if h : n = 6930 then
    subst h; exact five_le_a_6930
  else if h : n = 6936 then
    subst h; exact five_le_a_6936
  else if h : n = 6942 then
    subst h; exact five_le_a_6942
  else if h : n = 6948 then
    subst h; exact five_le_a_6948
  else if h : n = 6954 then
    subst h; exact five_le_a_6954
  else if h : n = 6960 then
    subst h; exact five_le_a_6960
  else if h : n = 6966 then
    subst h; exact five_le_a_6966
  else if h : n = 6972 then
    subst h; exact five_le_a_6972
  else if h : n = 6978 then
    subst h; exact five_le_a_6978
  else if h : n = 6984 then
    subst h; exact five_le_a_6984
  else if h : n = 6990 then
    subst h; exact five_le_a_6990
  else if h : n = 6996 then
    subst h; exact five_le_a_6996
  else if h : n = 7002 then
    subst h; exact five_le_a_7002
  else if h : n = 7008 then
    subst h; exact five_le_a_7008
  else if h : n = 7014 then
    subst h; exact five_le_a_7014
  else if h : n = 7020 then
    subst h; exact five_le_a_7020
  else if h : n = 7026 then
    subst h; exact five_le_a_7026
  else if h : n = 7032 then
    subst h; exact five_le_a_7032
  else if h : n = 7038 then
    subst h; exact five_le_a_7038
  else if h : n = 7044 then
    subst h; exact five_le_a_7044
  else if h : n = 7050 then
    subst h; exact five_le_a_7050
  else if h : n = 7056 then
    subst h; exact five_le_a_7056
  else if h : n = 7062 then
    subst h; exact five_le_a_7062
  else if h : n = 7068 then
    subst h; exact five_le_a_7068
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_47 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7074 ≤ n) (hle : n ≤ 7218) : 5 ≤ a n := by
  if h : n = 7074 then
    subst h; exact five_le_a_7074
  else if h : n = 7080 then
    subst h; exact five_le_a_7080
  else if h : n = 7086 then
    subst h; exact five_le_a_7086
  else if h : n = 7092 then
    subst h; exact five_le_a_7092
  else if h : n = 7098 then
    subst h; exact five_le_a_7098
  else if h : n = 7104 then
    subst h; exact five_le_a_7104
  else if h : n = 7110 then
    subst h; exact five_le_a_7110
  else if h : n = 7116 then
    subst h; exact five_le_a_7116
  else if h : n = 7122 then
    subst h; exact five_le_a_7122
  else if h : n = 7128 then
    subst h; exact five_le_a_7128
  else if h : n = 7134 then
    subst h; exact five_le_a_7134
  else if h : n = 7140 then
    subst h; exact five_le_a_7140
  else if h : n = 7146 then
    subst h; exact five_le_a_7146
  else if h : n = 7152 then
    subst h; exact five_le_a_7152
  else if h : n = 7158 then
    subst h; exact five_le_a_7158
  else if h : n = 7164 then
    subst h; exact five_le_a_7164
  else if h : n = 7170 then
    subst h; exact five_le_a_7170
  else if h : n = 7176 then
    subst h; exact five_le_a_7176
  else if h : n = 7182 then
    subst h; exact five_le_a_7182
  else if h : n = 7188 then
    subst h; exact five_le_a_7188
  else if h : n = 7194 then
    subst h; exact five_le_a_7194
  else if h : n = 7200 then
    subst h; exact five_le_a_7200
  else if h : n = 7206 then
    subst h; exact five_le_a_7206
  else if h : n = 7212 then
    subst h; exact five_le_a_7212
  else if h : n = 7218 then
    subst h; exact five_le_a_7218
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_48 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7224 ≤ n) (hle : n ≤ 7368) : 5 ≤ a n := by
  if h : n = 7224 then
    subst h; exact five_le_a_7224
  else if h : n = 7230 then
    subst h; exact five_le_a_7230
  else if h : n = 7236 then
    subst h; exact five_le_a_7236
  else if h : n = 7242 then
    subst h; exact five_le_a_7242
  else if h : n = 7248 then
    subst h; exact five_le_a_7248
  else if h : n = 7254 then
    subst h; exact five_le_a_7254
  else if h : n = 7260 then
    subst h; exact five_le_a_7260
  else if h : n = 7266 then
    subst h; exact five_le_a_7266
  else if h : n = 7272 then
    subst h; exact five_le_a_7272
  else if h : n = 7278 then
    subst h; exact five_le_a_7278
  else if h : n = 7284 then
    subst h; exact five_le_a_7284
  else if h : n = 7290 then
    subst h; exact five_le_a_7290
  else if h : n = 7296 then
    subst h; exact five_le_a_7296
  else if h : n = 7302 then
    subst h; exact five_le_a_7302
  else if h : n = 7308 then
    subst h; exact five_le_a_7308
  else if h : n = 7314 then
    subst h; exact five_le_a_7314
  else if h : n = 7320 then
    subst h; exact five_le_a_7320
  else if h : n = 7326 then
    subst h; exact five_le_a_7326
  else if h : n = 7332 then
    subst h; exact five_le_a_7332
  else if h : n = 7338 then
    subst h; exact five_le_a_7338
  else if h : n = 7344 then
    subst h; exact five_le_a_7344
  else if h : n = 7350 then
    subst h; exact five_le_a_7350
  else if h : n = 7356 then
    subst h; exact five_le_a_7356
  else if h : n = 7362 then
    subst h; exact five_le_a_7362
  else if h : n = 7368 then
    subst h; exact five_le_a_7368
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_49 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7374 ≤ n) (hle : n ≤ 7518) : 5 ≤ a n := by
  if h : n = 7374 then
    subst h; exact five_le_a_7374
  else if h : n = 7380 then
    subst h; exact five_le_a_7380
  else if h : n = 7386 then
    subst h; exact five_le_a_7386
  else if h : n = 7392 then
    subst h; exact five_le_a_7392
  else if h : n = 7398 then
    subst h; exact five_le_a_7398
  else if h : n = 7404 then
    subst h; exact five_le_a_7404
  else if h : n = 7410 then
    subst h; exact five_le_a_7410
  else if h : n = 7416 then
    subst h; exact five_le_a_7416
  else if h : n = 7422 then
    subst h; exact five_le_a_7422
  else if h : n = 7428 then
    subst h; exact five_le_a_7428
  else if h : n = 7434 then
    subst h; exact five_le_a_7434
  else if h : n = 7440 then
    subst h; exact five_le_a_7440
  else if h : n = 7446 then
    subst h; exact five_le_a_7446
  else if h : n = 7452 then
    subst h; exact five_le_a_7452
  else if h : n = 7458 then
    subst h; exact five_le_a_7458
  else if h : n = 7464 then
    subst h; exact five_le_a_7464
  else if h : n = 7470 then
    subst h; exact five_le_a_7470
  else if h : n = 7476 then
    subst h; exact five_le_a_7476
  else if h : n = 7482 then
    subst h; exact five_le_a_7482
  else if h : n = 7488 then
    subst h; exact five_le_a_7488
  else if h : n = 7494 then
    subst h; exact five_le_a_7494
  else if h : n = 7500 then
    subst h; exact five_le_a_7500
  else if h : n = 7506 then
    subst h; exact five_le_a_7506
  else if h : n = 7512 then
    subst h; exact five_le_a_7512
  else if h : n = 7518 then
    subst h; exact five_le_a_7518
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_50 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7524 ≤ n) (hle : n ≤ 7668) : 5 ≤ a n := by
  if h : n = 7524 then
    subst h; exact five_le_a_7524
  else if h : n = 7530 then
    subst h; exact five_le_a_7530
  else if h : n = 7536 then
    subst h; exact five_le_a_7536
  else if h : n = 7542 then
    subst h; exact five_le_a_7542
  else if h : n = 7548 then
    subst h; exact five_le_a_7548
  else if h : n = 7554 then
    subst h; exact five_le_a_7554
  else if h : n = 7560 then
    subst h; exact five_le_a_7560
  else if h : n = 7566 then
    subst h; exact five_le_a_7566
  else if h : n = 7572 then
    subst h; exact five_le_a_7572
  else if h : n = 7578 then
    subst h; exact five_le_a_7578
  else if h : n = 7584 then
    subst h; exact five_le_a_7584
  else if h : n = 7590 then
    subst h; exact five_le_a_7590
  else if h : n = 7596 then
    subst h; exact five_le_a_7596
  else if h : n = 7602 then
    subst h; exact five_le_a_7602
  else if h : n = 7608 then
    subst h; exact five_le_a_7608
  else if h : n = 7614 then
    subst h; exact five_le_a_7614
  else if h : n = 7620 then
    subst h; exact five_le_a_7620
  else if h : n = 7626 then
    subst h; exact five_le_a_7626
  else if h : n = 7632 then
    subst h; exact five_le_a_7632
  else if h : n = 7638 then
    subst h; exact five_le_a_7638
  else if h : n = 7644 then
    subst h; exact five_le_a_7644
  else if h : n = 7650 then
    subst h; exact five_le_a_7650
  else if h : n = 7656 then
    subst h; exact five_le_a_7656
  else if h : n = 7662 then
    subst h; exact five_le_a_7662
  else if h : n = 7668 then
    subst h; exact five_le_a_7668
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_51 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7674 ≤ n) (hle : n ≤ 7818) : 5 ≤ a n := by
  if h : n = 7674 then
    subst h; exact five_le_a_7674
  else if h : n = 7680 then
    subst h; exact five_le_a_7680
  else if h : n = 7686 then
    subst h; exact five_le_a_7686
  else if h : n = 7692 then
    subst h; exact five_le_a_7692
  else if h : n = 7698 then
    subst h; exact five_le_a_7698
  else if h : n = 7704 then
    subst h; exact five_le_a_7704
  else if h : n = 7710 then
    subst h; exact five_le_a_7710
  else if h : n = 7716 then
    subst h; exact five_le_a_7716
  else if h : n = 7722 then
    subst h; exact five_le_a_7722
  else if h : n = 7728 then
    subst h; exact five_le_a_7728
  else if h : n = 7734 then
    subst h; exact five_le_a_7734
  else if h : n = 7740 then
    subst h; exact five_le_a_7740
  else if h : n = 7746 then
    subst h; exact five_le_a_7746
  else if h : n = 7752 then
    subst h; exact five_le_a_7752
  else if h : n = 7758 then
    subst h; exact five_le_a_7758
  else if h : n = 7764 then
    subst h; exact five_le_a_7764
  else if h : n = 7770 then
    subst h; exact five_le_a_7770
  else if h : n = 7776 then
    subst h; exact five_le_a_7776
  else if h : n = 7782 then
    subst h; exact five_le_a_7782
  else if h : n = 7788 then
    subst h; exact five_le_a_7788
  else if h : n = 7794 then
    subst h; exact five_le_a_7794
  else if h : n = 7800 then
    subst h; exact five_le_a_7800
  else if h : n = 7806 then
    subst h; exact five_le_a_7806
  else if h : n = 7812 then
    subst h; exact five_le_a_7812
  else if h : n = 7818 then
    subst h; exact five_le_a_7818
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_52 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7824 ≤ n) (hle : n ≤ 7968) : 5 ≤ a n := by
  if h : n = 7824 then
    subst h; exact five_le_a_7824
  else if h : n = 7830 then
    subst h; exact five_le_a_7830
  else if h : n = 7836 then
    subst h; exact five_le_a_7836
  else if h : n = 7842 then
    subst h; exact five_le_a_7842
  else if h : n = 7848 then
    subst h; exact five_le_a_7848
  else if h : n = 7854 then
    subst h; exact five_le_a_7854
  else if h : n = 7860 then
    subst h; exact five_le_a_7860
  else if h : n = 7866 then
    subst h; exact five_le_a_7866
  else if h : n = 7872 then
    subst h; exact five_le_a_7872
  else if h : n = 7878 then
    subst h; exact five_le_a_7878
  else if h : n = 7884 then
    subst h; exact five_le_a_7884
  else if h : n = 7890 then
    subst h; exact five_le_a_7890
  else if h : n = 7896 then
    subst h; exact five_le_a_7896
  else if h : n = 7902 then
    subst h; exact five_le_a_7902
  else if h : n = 7908 then
    subst h; exact five_le_a_7908
  else if h : n = 7914 then
    subst h; exact five_le_a_7914
  else if h : n = 7920 then
    subst h; exact five_le_a_7920
  else if h : n = 7926 then
    subst h; exact five_le_a_7926
  else if h : n = 7932 then
    subst h; exact five_le_a_7932
  else if h : n = 7938 then
    subst h; exact five_le_a_7938
  else if h : n = 7944 then
    subst h; exact five_le_a_7944
  else if h : n = 7950 then
    subst h; exact five_le_a_7950
  else if h : n = 7956 then
    subst h; exact five_le_a_7956
  else if h : n = 7962 then
    subst h; exact five_le_a_7962
  else if h : n = 7968 then
    subst h; exact five_le_a_7968
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_chunk_53 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 7974 ≤ n) (hle : n ≤ 7998) : 5 ≤ a n := by
  if h : n = 7974 then
    subst h; exact five_le_a_7974
  else if h : n = 7980 then
    subst h; exact five_le_a_7980
  else if h : n = 7986 then
    subst h; exact five_le_a_7986
  else if h : n = 7992 then
    subst h; exact five_le_a_7992
  else if h : n = 7998 then
    subst h; exact five_le_a_7998
  else
    have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega

lemma five_le_a_of_dvd_six_ge_24_le_8000 {n : ℕ}
    (h6 : 6 ∣ n) (hge : 24 ≤ n) (hle : n ≤ 8000) : 5 ≤ a n := by
  if h : n ≤ 168 then
    exact five_le_a_chunk_0 h6 (by omega) h
  else if h : n ≤ 318 then
    exact five_le_a_chunk_1 h6 (by omega) h
  else if h : n ≤ 468 then
    exact five_le_a_chunk_2 h6 (by omega) h
  else if h : n ≤ 618 then
    exact five_le_a_chunk_3 h6 (by omega) h
  else if h : n ≤ 768 then
    exact five_le_a_chunk_4 h6 (by omega) h
  else if h : n ≤ 918 then
    exact five_le_a_chunk_5 h6 (by omega) h
  else if h : n ≤ 1068 then
    exact five_le_a_chunk_6 h6 (by omega) h
  else if h : n ≤ 1218 then
    exact five_le_a_chunk_7 h6 (by omega) h
  else if h : n ≤ 1368 then
    exact five_le_a_chunk_8 h6 (by omega) h
  else if h : n ≤ 1518 then
    exact five_le_a_chunk_9 h6 (by omega) h
  else if h : n ≤ 1668 then
    exact five_le_a_chunk_10 h6 (by omega) h
  else if h : n ≤ 1818 then
    exact five_le_a_chunk_11 h6 (by omega) h
  else if h : n ≤ 1968 then
    exact five_le_a_chunk_12 h6 (by omega) h
  else if h : n ≤ 2118 then
    exact five_le_a_chunk_13 h6 (by omega) h
  else if h : n ≤ 2268 then
    exact five_le_a_chunk_14 h6 (by omega) h
  else if h : n ≤ 2418 then
    exact five_le_a_chunk_15 h6 (by omega) h
  else if h : n ≤ 2568 then
    exact five_le_a_chunk_16 h6 (by omega) h
  else if h : n ≤ 2718 then
    exact five_le_a_chunk_17 h6 (by omega) h
  else if h : n ≤ 2868 then
    exact five_le_a_chunk_18 h6 (by omega) h
  else if h : n ≤ 3018 then
    exact five_le_a_chunk_19 h6 (by omega) h
  else if h : n ≤ 3168 then
    exact five_le_a_chunk_20 h6 (by omega) h
  else if h : n ≤ 3318 then
    exact five_le_a_chunk_21 h6 (by omega) h
  else if h : n ≤ 3468 then
    exact five_le_a_chunk_22 h6 (by omega) h
  else if h : n ≤ 3618 then
    exact five_le_a_chunk_23 h6 (by omega) h
  else if h : n ≤ 3768 then
    exact five_le_a_chunk_24 h6 (by omega) h
  else if h : n ≤ 3918 then
    exact five_le_a_chunk_25 h6 (by omega) h
  else if h : n ≤ 4068 then
    exact five_le_a_chunk_26 h6 (by omega) h
  else if h : n ≤ 4218 then
    exact five_le_a_chunk_27 h6 (by omega) h
  else if h : n ≤ 4368 then
    exact five_le_a_chunk_28 h6 (by omega) h
  else if h : n ≤ 4518 then
    exact five_le_a_chunk_29 h6 (by omega) h
  else if h : n ≤ 4668 then
    exact five_le_a_chunk_30 h6 (by omega) h
  else if h : n ≤ 4818 then
    exact five_le_a_chunk_31 h6 (by omega) h
  else if h : n ≤ 4968 then
    exact five_le_a_chunk_32 h6 (by omega) h
  else if h : n ≤ 5118 then
    exact five_le_a_chunk_33 h6 (by omega) h
  else if h : n ≤ 5268 then
    exact five_le_a_chunk_34 h6 (by omega) h
  else if h : n ≤ 5418 then
    exact five_le_a_chunk_35 h6 (by omega) h
  else if h : n ≤ 5568 then
    exact five_le_a_chunk_36 h6 (by omega) h
  else if h : n ≤ 5718 then
    exact five_le_a_chunk_37 h6 (by omega) h
  else if h : n ≤ 5868 then
    exact five_le_a_chunk_38 h6 (by omega) h
  else if h : n ≤ 6018 then
    exact five_le_a_chunk_39 h6 (by omega) h
  else if h : n ≤ 6168 then
    exact five_le_a_chunk_40 h6 (by omega) h
  else if h : n ≤ 6318 then
    exact five_le_a_chunk_41 h6 (by omega) h
  else if h : n ≤ 6468 then
    exact five_le_a_chunk_42 h6 (by omega) h
  else if h : n ≤ 6618 then
    exact five_le_a_chunk_43 h6 (by omega) h
  else if h : n ≤ 6768 then
    exact five_le_a_chunk_44 h6 (by omega) h
  else if h : n ≤ 6918 then
    exact five_le_a_chunk_45 h6 (by omega) h
  else if h : n ≤ 7068 then
    exact five_le_a_chunk_46 h6 (by omega) h
  else if h : n ≤ 7218 then
    exact five_le_a_chunk_47 h6 (by omega) h
  else if h : n ≤ 7368 then
    exact five_le_a_chunk_48 h6 (by omega) h
  else if h : n ≤ 7518 then
    exact five_le_a_chunk_49 h6 (by omega) h
  else if h : n ≤ 7668 then
    exact five_le_a_chunk_50 h6 (by omega) h
  else if h : n ≤ 7818 then
    exact five_le_a_chunk_51 h6 (by omega) h
  else if h : n ≤ 7968 then
    exact five_le_a_chunk_52 h6 (by omega) h
  else
    exact five_le_a_chunk_53 h6 (by omega) (by omega)

lemma a_ne_four_of_dvd_six_of_lt_24 {n : ℕ} (h6 : 6 ∣ n) (h : n < 24) : a n ≠ 4 := by
  have : n % 6 = 0 := Nat.mod_eq_zero_of_dvd h6
  interval_cases n <;> decide

lemma a_ne_four_of_dvd_six_of_le_8000 {n : ℕ} (h6 : 6 ∣ n) (hle : n ≤ 8000) : a n ≠ 4 := by
  by_cases hlt : n < 24
  · exact a_ne_four_of_dvd_six_of_lt_24 h6 hlt
  · have : 5 ≤ a n := five_le_a_of_dvd_six_ge_24_le_8000 h6 (by omega) hle
    omega

/-- If `6 ∣ n` and `n > 6` then `2` is not in `Sset n`. -/
lemma two_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 2 ∉ Sset n := by
  intro h
  have hsum : (n + 2).Prime := (mem_Sset_iff.mp h).2.2.2
  have heven : Even (n + 2) := (even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 6) h6)).add even_two
  have hne2 : n + 2 ≠ 2 := by omega
  exact not_prime_of_even_of_ne_two heven hne2 hsum

/-- If `6 ∣ n` and `n > 6` then `3` is not in `Sset n`. -/
lemma three_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 3 ∉ Sset n := by
  intro h
  have hsum : (n + 3).Prime := (mem_Sset_iff.mp h).2.2.2
  have hdvd : 3 ∣ n + 3 := (dvd_trans (by decide : 3 ∣ 6) h6).add (dvd_refl 3)
  have hgt : 3 < n + 3 := by omega
  exact not_prime_of_dvd_of_lt hdvd (by norm_num) hgt hsum

/-- Elements of `Sset n` are at least `5` when `6 ∣ n` and `n > 6`. -/
lemma five_le_of_mem_Sset_of_dvd_six {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Sset n) : 5 ≤ q := by
  have hP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have hq2 : q ≠ 2 := fun h => two_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  have hq3 : q ≠ 3 := fun h => three_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  exact hP.five_le_of_ne_two_of_ne_three hq2 hq3

/-- Pairing: if `q ∈ Sset n` then `n - q ∈ Sset n` iff `2 * n - q` is prime. -/
lemma sub_mem_Sset_iff {n q : ℕ} (hq : q ∈ Sset n) :
    n - q ∈ Sset n ↔ (2 * n - q).Prime := by
  have h := mem_Sset_iff.mp hq
  have hqlt : q < n := h.1
  have hqP : q.Prime := h.2.1
  have hdiffP : (n - q).Prime := h.2.2.1
  have hqpos : 0 < q := hqP.pos
  have hsum : n + (n - q) = 2 * n - q := by
    rw [← Nat.add_sub_assoc (le_of_lt hqlt), ← Nat.two_mul]
  constructor
  · intro hnq
    have h2 := mem_Sset_iff.mp hnq
    simpa [hsum] using h2.2.2.2
  · intro h2n
    apply mem_Sset_of_primes
    · exact Nat.sub_lt (lt_trans hqpos hqlt) hqpos
    · exact hdiffP
    · simpa [Nat.sub_sub_self (le_of_lt hqlt)] using hqP
    · simpa [hsum] using h2n

/-- `q` is paired in `Sset n` if both `q` and `n - q` lie in `Sset n`. -/
def IsPaired (n q : ℕ) : Prop := q ∈ Sset n ∧ n - q ∈ Sset n

lemma isPaired_iff {n q : ℕ} (hq : q ∈ Sset n) :
    IsPaired n q ↔ (2 * n - q).Prime := by
  unfold IsPaired
  constructor
  · intro h
    exact (sub_mem_Sset_iff hq).mp h.2
  · intro hp
    exact ⟨hq, (sub_mem_Sset_iff hq).mpr hp⟩

lemma isPaired_sub {n q : ℕ} (h : IsPaired n q) : IsPaired n (n - q) := by
  have hq : q ∈ Sset n := h.1
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have : n - (n - q) = q := Nat.sub_sub_self (le_of_lt hqlt)
  refine ⟨h.2, ?_⟩
  simpa [this] using hq

lemma not_eq_sub_self_of_mem_Sset {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Sset n) : q ≠ n - q := by
  intro heq
  have hn2q : n = 2 * q := by omega
  have hqP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have h3 : 3 ∣ n := dvd_trans (by decide : 3 ∣ 6) h6
  have h3q : 3 ∣ q := by
    have : 3 ∣ 2 * q := hn2q ▸ h3
    exact (Nat.Prime.dvd_mul prime_three).mp this |>.resolve_left (by decide)
  have hq3 : 3 < q := by
    have : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hq
    omega
  exact (not_prime_of_dvd_of_lt h3q (by norm_num) hq3) hqP

/-- The pairing involution `q ↦ n - q` on `Sset n`. -/
def pairMap (n : ℕ) (q : ℕ) : ℕ := n - q

lemma pairMap_mem_of_isPaired {n q : ℕ} (h : IsPaired n q) :
    pairMap n q ∈ Sset n := h.2

lemma pairMap_sq {n q : ℕ} (hq : q < n) : pairMap n (pairMap n q) = q :=
  Nat.sub_sub_self (le_of_lt hq)

/-- Unpaired elements of `Sset n`. -/
def Unpaired (n : ℕ) : Finset ℕ :=
  (Sset n).filter (fun q => n - q ∉ Sset n)

/-- Paired elements of `Sset n`. -/
def Paired (n : ℕ) : Finset ℕ :=
  (Sset n).filter (fun q => n - q ∈ Sset n)

lemma mem_Unpaired_iff {n q : ℕ} :
    q ∈ Unpaired n ↔ q ∈ Sset n ∧ n - q ∉ Sset n := by
  simp [Unpaired, mem_filter]

lemma mem_Paired_iff {n q : ℕ} :
    q ∈ Paired n ↔ q ∈ Sset n ∧ n - q ∈ Sset n := by
  simp [Paired, mem_filter]

lemma paired_union_unpaired (n : ℕ) : Paired n ∪ Unpaired n = Sset n := by
  ext q
  simp [Paired, Unpaired, mem_filter, mem_union]
  tauto

lemma paired_disj_unpaired (n : ℕ) : Disjoint (Paired n) (Unpaired n) := by
  refine Finset.disjoint_left.mpr ?_
  intro q hqP hqU
  exact (mem_Unpaired_iff.mp hqU).2 (mem_Paired_iff.mp hqP).2

lemma card_Sset_eq_paired_add_unpaired (n : ℕ) :
    #(Sset n) = #(Paired n) + #(Unpaired n) := by
  rw [← card_union_of_disjoint (paired_disj_unpaired n), paired_union_unpaired]

lemma pairMap_mem_paired {n q : ℕ} (hq : q ∈ Paired n) :
    n - q ∈ Paired n := by
  have h := mem_Paired_iff.mp hq
  have hqlt : q < n := (mem_Sset_iff.mp h.1).1
  refine mem_Paired_iff.mpr ⟨h.2, ?_⟩
  simpa [Nat.sub_sub_self (le_of_lt hqlt)] using h.1

lemma pairMap_ne_self_of_mem_paired {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Paired n) : n - q ≠ q := by
  have : q ∈ Sset n := (mem_Paired_iff.mp hq).1
  exact (not_eq_sub_self_of_mem_Sset h6 hn this).symm

lemma paired_lt_or_gt {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) (hq : q ∈ Paired n) :
    q < n - q ∨ n - q < q := by
  have hne : n - q ≠ q := pairMap_ne_self_of_mem_paired h6 hn hq
  omega

/-- Representatives of pairing orbits: the smaller element of each pair. -/
def PairedRep (n : ℕ) : Finset ℕ :=
  (Paired n).filter (fun q => q < n - q)

lemma mem_PairedRep_iff {n q : ℕ} :
    q ∈ PairedRep n ↔ q ∈ Paired n ∧ q < n - q := by
  simp [PairedRep, mem_filter]

lemma paired_eq_reps_union_image {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    Paired n = PairedRep n ∪ (PairedRep n).image (fun q => n - q) := by
  ext q
  constructor
  · intro hq
    rcases paired_lt_or_gt h6 hn hq with hlt | hgt
    · exact mem_union.mpr (Or.inl (mem_PairedRep_iff.mpr ⟨hq, hlt⟩))
    · refine mem_union.mpr (Or.inr ?_)
      refine mem_image.mpr ⟨n - q, ?_, ?_⟩
      · have hqlt : q < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hq).1).1
        have : n - (n - q) = q := Nat.sub_sub_self (le_of_lt hqlt)
        refine mem_PairedRep_iff.mpr ⟨pairMap_mem_paired hq, ?_⟩
        simpa [this] using hgt
      · have hqlt : q < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hq).1).1
        exact Nat.sub_sub_self (le_of_lt hqlt)
  · intro h
    rcases mem_union.mp h with h | h
    · exact (mem_PairedRep_iff.mp h).1
    · rcases mem_image.mp h with ⟨r, hr, rfl⟩
      exact pairMap_mem_paired (mem_PairedRep_iff.mp hr).1

lemma disjoint_reps_image {n : ℕ} (_h6 : 6 ∣ n) (_hn : 6 < n) :
    Disjoint (PairedRep n) ((PairedRep n).image (fun q => n - q)) := by
  refine Finset.disjoint_left.mpr ?_
  intro q hq1 hq2
  have h1 := mem_PairedRep_iff.mp hq1
  rcases mem_image.mp hq2 with ⟨r, hr, rfl⟩
  have h2 := mem_PairedRep_iff.mp hr
  have hrlt : r < n := (mem_Sset_iff.mp (mem_Paired_iff.mp h2.1).1).1
  have hlt : n - r < r := by
    have : n - r < n - (n - r) := h1.2
    simpa [Nat.sub_sub_self (le_of_lt hrlt)] using this
  exact lt_asymm h2.2 hlt

lemma card_image_sub_reps {n : ℕ} :
    #((PairedRep n).image (fun q => n - q)) = #(PairedRep n) := by
  refine Finset.card_image_iff.mpr ?_
  intro a ha b hb h
  have ha' := mem_PairedRep_iff.mp ha
  have hb' := mem_PairedRep_iff.mp hb
  have halt : a < n := (mem_Sset_iff.mp (mem_Paired_iff.mp ha'.1).1).1
  have hblt : b < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hb'.1).1).1
  have haeq : n - (n - a) = a := Nat.sub_sub_self (le_of_lt halt)
  have hbeq : n - (n - b) = b := Nat.sub_sub_self (le_of_lt hblt)
  have h' : n - a = n - b := h
  rw [← haeq, ← hbeq, h']

/-- `Paired n` is a union of 2-cycles, hence even cardinality when `6 ∣ n` and `n > 6`. -/
lemma even_card_Paired {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : Even #(Paired n) := by
  have hunion := paired_eq_reps_union_image h6 hn
  have hdisj := disjoint_reps_image h6 hn
  have hcard : #(Paired n) = 2 * #(PairedRep n) := by
    rw [hunion, card_union_of_disjoint hdisj, card_image_sub_reps]
    ring
  exact ⟨#(PairedRep n), by omega⟩

lemma a_eq_two_mul_P_add_U {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    a n = 2 * (#(Paired n) / 2) + #(Unpaired n) := by
  rw [a_eq_card_Sset, card_Sset_eq_paired_add_unpaired]
  have he : Even #(Paired n) := even_card_Paired h6 hn
  have : 2 * (#(Paired n) / 2) = #(Paired n) := Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  omega

/-- The three configurations that would give `a n = 4`. -/
lemma a_eq_four_config {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) (ha : a n = 4) :
    (#(Paired n) = 4 ∧ #(Unpaired n) = 0) ∨
    (#(Paired n) = 2 ∧ #(Unpaired n) = 2) ∨
    (#(Paired n) = 0 ∧ #(Unpaired n) = 4) := by
  have hsum : #(Paired n) + #(Unpaired n) = 4 := by
    rw [← card_Sset_eq_paired_add_unpaired, ← a_eq_card_Sset, ha]
  have he : Even #(Paired n) := even_card_Paired h6 hn
  have hP4 : #(Paired n) ≤ 4 := by omega
  have : #(Paired n) = 0 ∨ #(Paired n) = 2 ∨ #(Paired n) = 4 := by
    have : #(Paired n) % 2 = 0 := Nat.even_iff.mp he
    interval_cases #(Paired n) <;> simp_all
  rcases this with h0 | h2 | h4
  · right; right; omega
  · right; left; omega
  · left; omega

/-- If a prime `p` divides `n` and `2 < p < n`, then `p ∉ Sset n`. -/
lemma not_mem_Sset_of_dvd {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ n) (_h2 : 2 < p)
    (_hpn : p < n) : p ∉ Sset n := by
  intro h
  have hsum : (n + p).Prime := (mem_Sset_iff.mp h).2.2.2
  have hdiv : p ∣ n + p := hdvd.add (dvd_refl p)
  have hgt : p < n + p := by omega
  exact not_prime_of_dvd_of_lt hdiv hp.two_le hgt hsum

lemma prime_mod_five_ne_zero {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : p % 5 ≠ 0 := by
  intro h0
  have hdvd : 5 ∣ p := Nat.dvd_iff_mod_eq_zero.2 h0
  have heq : 5 = p := (prime_dvd_prime_iff_eq prime_five hp).mp hdvd
  exact h5 heq.symm

/-- Elements of `Sset n` other than `5` are nonzero modulo `5`. -/
lemma mem_Sset_mod_five_ne_zero {n q : ℕ} (hq : q ∈ Sset n) (hne5 : q ≠ 5) :
    q % 5 ≠ 0 :=
  prime_mod_five_ne_zero (mem_Sset_iff.mp hq).2.1 hne5

lemma card_PairedRep_of_card_Paired {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    #(Paired n) = 2 * #(PairedRep n) := by
  have hunion := paired_eq_reps_union_image h6 hn
  have hdisj := disjoint_reps_image h6 hn
  rw [hunion, card_union_of_disjoint hdisj, card_image_sub_reps]
  ring

lemma pairedRep_card_two_of_paired_four {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) : #(PairedRep n) = 2 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma pairedRep_card_one_of_paired_two {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 2) : #(PairedRep n) = 1 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma pairedRep_card_zero_of_paired_zero {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 0) : #(PairedRep n) = 0 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma exists_two_pairedReps {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) :
    ∃ r s, r ∈ PairedRep n ∧ s ∈ PairedRep n ∧ r ≠ s := by
  have hcard : #(PairedRep n) = 2 := pairedRep_card_two_of_paired_four h6 hn hP
  have hne : (PairedRep n).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [h] at hcard
  obtain ⟨r, hr⟩ := hne
  have hrest : (PairedRep n).erase r ≠ ∅ := by
    intro h
    have := card_erase_of_mem hr
    simp [hcard] at this
    simp [h] at this
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hrest
  refine ⟨r, s, hr, mem_of_mem_erase hs, ?_⟩
  exact (ne_of_mem_erase hs).symm

/-- The eight primes attached to two pairing representatives. -/
lemma eight_primes_of_two_reps {n r s : ℕ} (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) :
    r.Prime ∧ (n - r).Prime ∧ (n + r).Prime ∧ (2 * n - r).Prime ∧
    s.Prime ∧ (n - s).Prime ∧ (n + s).Prime ∧ (2 * n - s).Prime := by
  have hrP := mem_PairedRep_iff.mp hr
  have hsP := mem_PairedRep_iff.mp hs
  have hrS : r ∈ Sset n := (mem_Paired_iff.mp hrP.1).1
  have hsS : s ∈ Sset n := (mem_Paired_iff.mp hsP.1).1
  have hr2 := (isPaired_iff hrS).mp ⟨hrS, (mem_Paired_iff.mp hrP.1).2⟩
  have hs2 := (isPaired_iff hsS).mp ⟨hsS, (mem_Paired_iff.mp hsP.1).2⟩
  exact ⟨(mem_Sset_iff.mp hrS).2.1, (mem_Sset_iff.mp hrS).2.2.1,
    (mem_Sset_iff.mp hrS).2.2.2, hr2,
    (mem_Sset_iff.mp hsS).2.1, (mem_Sset_iff.mp hsS).2.2.1,
    (mem_Sset_iff.mp hsS).2.2.2, hs2⟩

/-- The four diamond values attached to a pairing representative are prime. -/
lemma four_primes_of_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) :
    r.Prime ∧ (n - r).Prime ∧ (n + r).Prime ∧ (2 * n - r).Prime := by
  have h := eight_primes_of_two_reps hr hr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

lemma not_dvd_five_of_prime_gt_five {m : ℕ} (hp : m.Prime) (hgt : 5 < m) : ¬ 5 ∣ m := by
  intro hd
  have : 5 = m := (prime_dvd_prime_iff_eq prime_five hp).mp hd
  omega

/-- If `5 ∤ n` and `r ∈ PairedRep n` with `r ≠ 5`, then `r ≡ 3 * n (mod 5)`. -/
lemma pairedRep_mod_five {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn5 : ¬ 5 ∣ n) (hr5 : r ≠ 5) :
    r % 5 = (3 * n) % 5 := by
  have hP := mem_PairedRep_iff.mp hr
  have ⟨hrp, hnrp, hnpr, h2nr⟩ := four_primes_of_pairedRep hr
  have hqlt : r < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hP.1).1).1
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn (mem_Paired_iff.mp hP.1).1
  have hn0 : n % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 hn5
  have hr0 : r % 5 ≠ 0 := prime_mod_five_ne_zero hrp hr5
  have hsub0 : (n - r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five hnrp (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have hadd0 : (n + r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five hnpr (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have h2n0 : (2 * n - r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five h2nr (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have hrle : r ≤ n := Nat.le_of_lt hqlt
  have h2nle : r ≤ 2 * n := by omega
  -- Rewrite the three forbidden congruences in terms of `% 5`.
  have hadd_mod : (n % 5 + r % 5) % 5 ≠ 0 := by
    rw [← Nat.add_mod]; exact hadd0
  have hsub_mod : (n % 5 + 5 - r % 5) % 5 ≠ 0 := by
    have hnr : (n - r) % 5 = (n % 5 + 5 - r % 5) % 5 := by
      have := Nat.mod_add_div n 5
      have := Nat.mod_add_div r 5
      omega
    simpa [hnr] using hsub0
  have h2n_mod : (2 * (n % 5) + 5 - r % 5) % 5 ≠ 0 := by
    have : (2 * n - r) % 5 = (2 * (n % 5) + 5 - r % 5) % 5 := by
      omega
    simpa [this] using h2n0
  have hnlt : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hrlt5 : r % 5 < 5 := Nat.mod_lt _ (by decide)
  have hn1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hr1 : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by omega
  rcases hn1 with hn1 | hn1 | hn1 | hn1 <;> rcases hr1 with hr1 | hr1 | hr1 | hr1 <;>
    simp [hn1, hr1, Nat.mul_mod] at hadd_mod hsub_mod h2n_mod ⊢

lemma two_pairedReps_congruent_mod_five {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hn5 : ¬ 5 ∣ n) (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    r % 5 = s % 5 := by
  rw [pairedRep_mod_five h6 hn hr hn5 hr5, pairedRep_mod_five h6 hn hs hn5 hs5]

lemma pairedRep_lt_half {n r : ℕ} (hr : r ∈ PairedRep n) : r < n - r :=
  (mem_PairedRep_iff.mp hr).2

lemma pairedRep_lt_n {n r : ℕ} (hr : r ∈ PairedRep n) : r < n := by
  have hS : r ∈ Sset n := (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).1
  exact (mem_Sset_iff.mp hS).1

lemma pairedRep_mem_Sset {n r : ℕ} (hr : r ∈ PairedRep n) : r ∈ Sset n :=
  (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).1

lemma sub_pairedRep_mem_Sset {n r : ℕ} (hr : r ∈ PairedRep n) : n - r ∈ Sset n :=
  (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).2

lemma unpaired_eq_empty_iff {n : ℕ} : Unpaired n = ∅ ↔ ∀ q ∈ Sset n, n - q ∈ Sset n := by
  constructor
  · intro h q hq
    by_contra hnq
    have : q ∈ Unpaired n := mem_Unpaired_iff.mpr ⟨hq, hnq⟩
    simp [h] at this
  · intro h
    ext q
    simp [mem_Unpaired_iff]
    intro hq
    exact h q hq

lemma Sset_eq_paired_of_unpaired_empty {n : ℕ} (h : Unpaired n = ∅) :
    Sset n = Paired n := by
  have := paired_union_unpaired n
  simpa [h] using this.symm

lemma five_mem_Sset_iff {n : ℕ} (hn : 5 < n) :
    5 ∈ Sset n ↔ (n - 5).Prime ∧ (n + 5).Prime := by
  constructor
  · intro h
    have := mem_Sset_iff.mp h
    exact ⟨this.2.2.1, this.2.2.2⟩
  · intro h
    exact mem_Sset_of_primes (by omega) prime_five h.1 h.2

lemma n_sub_five_mem_Sset_iff {n : ℕ} (hn : 5 < n) :
    n - 5 ∈ Sset n ↔ (n - 5).Prime ∧ (2 * n - 5).Prime := by
  constructor
  · intro h
    have := mem_Sset_iff.mp h
    have hsum : n + (n - 5) = 2 * n - 5 := by omega
    exact ⟨this.2.1, by simpa [hsum] using this.2.2.2⟩
  · intro h
    apply mem_Sset_of_primes
    · omega
    · exact h.1
    · simpa [Nat.sub_sub_self (by omega : 5 ≤ n)] using prime_five
    · have hsum : n + (n - 5) = 2 * n - 5 := by omega
      simpa [hsum] using h.2

/-- In the `(4,0)` configuration the Sset is exactly the two pairing orbits. -/
lemma Sset_eq_four_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    Sset n = {r, n - r, s, n - s} := by
  have hSeq : Sset n = Paired n := Sset_eq_paired_of_unpaired_empty hU
  have hcard : #(PairedRep n) = 2 := pairedRep_card_two_of_paired_four h6 hn hP
  have hsubset : {r, s} ⊆ PairedRep n := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : #({r, s} : Finset ℕ) = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simpa using hrs
  have hrs_eq : ({r, s} : Finset ℕ) = PairedRep n :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hunion := paired_eq_reps_union_image h6 hn
  rw [hSeq, hunion, ← hrs_eq]
  ext q
  constructor
  · intro h
    rcases mem_union.mp h with h | h
    · rcases mem_insert.mp h with rfl | h
      · simp
      · simp [mem_singleton.mp h]
    · rcases mem_image.mp h with ⟨a, ha, rfl⟩
      rcases mem_insert.mp ha with rfl | ha
      · simp
      · simp [mem_singleton.mp ha]
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact mem_union.mpr (Or.inl (by simp))
    · refine mem_union.mpr (Or.inr (mem_image.mpr ⟨r, by simp, rfl⟩))
    · exact mem_union.mpr (Or.inl (by simp))
    · refine mem_union.mpr (Or.inr (mem_image.mpr ⟨s, by simp, rfl⟩))

lemma eight_distinct_of_two_reps {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    r ≠ n - r ∧ r ≠ s ∧ r ≠ n - s ∧ r ≠ n + r ∧ r ≠ n + s ∧ r ≠ 2 * n - r ∧ r ≠ 2 * n - s ∧
    n - r ≠ s ∧ n - r ≠ n - s ∧ n - r ≠ n + r ∧ n - r ≠ n + s ∧ n - r ≠ 2 * n - r ∧
    n - r ≠ 2 * n - s ∧ s ≠ n - s ∧ s ≠ n + r ∧ s ≠ n + s ∧ s ≠ 2 * n - r ∧ s ≠ 2 * n - s ∧
    n - s ≠ n + r ∧ n - s ≠ n + s ∧ n - s ≠ 2 * n - r ∧ n - s ≠ 2 * n - s ∧
    n + r ≠ n + s ∧ n + r ≠ 2 * n - r ∧ n + r ≠ 2 * n - s ∧
    n + s ≠ 2 * n - r ∧ n + s ≠ 2 * n - s ∧ 2 * n - r ≠ 2 * n - s := by
  have hrlt := pairedRep_lt_half hr
  have hslt := pairedRep_lt_half hs
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hrS := pairedRep_mem_Sset hr
  have hsS := pairedRep_mem_Sset hs
  have hne_r := not_eq_sub_self_of_mem_Sset h6 hn hrS
  have hne_s := not_eq_sub_self_of_mem_Sset h6 hn hsS
  have h2r : 2 * r < n := by omega
  have h2s : 2 * s < n := by omega
  have hrs_lt : r + s < n := by omega
  have hrpos : 0 < r := (mem_Sset_iff.mp hrS).2.1.pos
  have hspos : 0 < s := (mem_Sset_iff.mp hsS).2.1.pos
  refine ⟨hne_r, hrs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne_s, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; omega)

/-- If `6 ∣ n` and `5 ∤ n` then `n` is `6,12,18` or `24` modulo `30`. -/
lemma mod_thirty_of_dvd_six_of_not_dvd_five {n : ℕ} (h6 : 6 ∣ n) (hn5 : ¬ 5 ∣ n) :
    n % 30 = 6 ∨ n % 30 = 12 ∨ n % 30 = 18 ∨ n % 30 = 24 := by
  have h30 : n % 30 < 30 := Nat.mod_lt _ (by decide)
  have h2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : 2 ∣ 6) h6)
  have h3 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : 3 ∣ 6) h6)
  have h5 : n % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 hn5
  have : n % 30 = 0 ∨ n % 30 = 6 ∨ n % 30 = 12 ∨ n % 30 = 18 ∨ n % 30 = 24 := by
    omega
  rcases this with h | h | h | h | h
  · have : n % 5 = 0 := by omega
    exact (h5 this).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma five_not_mem_Sset_of_dvd_five {n : ℕ} (h5 : 5 ∣ n) (hn : 5 < n) : 5 ∉ Sset n :=
  not_mem_Sset_of_dvd prime_five h5 (by decide) hn

/-- A pairing representative other than `5` is coprime to `30` when `6 ∣ n`. -/
lemma pairedRep_coprime_thirty {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hr5 : r ≠ 5) : ¬ 2 ∣ r ∧ ¬ 3 ∣ r ∧ ¬ 5 ∣ r := by
  have hrp := (four_primes_of_pairedRep hr).1
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn (pairedRep_mem_Sset hr)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : 2 = r := (prime_dvd_prime_iff_eq Nat.prime_two hrp).mp h
    omega
  · intro h
    have : 3 = r := (prime_dvd_prime_iff_eq prime_three hrp).mp h
    omega
  · intro h
    have : 5 = r := (prime_dvd_prime_iff_eq prime_five hrp).mp h
    exact hr5 this.symm

/-- If `n ≡ 6 (mod 30)` and `r ∈ PairedRep n` with `r ≠ 5`, then `r ≡ 13` or `23 (mod 30)`. -/
lemma pairedRep_mod_thirty_of_n_mod_six {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn6 : n % 30 = 6) (hr5 : r ≠ 5) :
    r % 30 = 13 ∨ r % 30 = 23 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hrlt : r % 30 < 30 := Nat.mod_lt _ (by decide)
  have hr2 : r % 2 = 1 := by
    have : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
    omega
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have hr5m : r % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by
      intro h
      have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h
      omega) hr5
  have : (3 * n) % 5 = 3 := by
    have : n % 5 = 1 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 3 := by omega
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_twelve {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn12 : n % 30 = 12) (hr5 : r ≠ 5) :
    r % 30 = 1 ∨ r % 30 = 11 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hrlt : r % 30 < 30 := Nat.mod_lt _ (by decide)
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 1 := by
    have : n % 5 = 2 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 1 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_eighteen {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn18 : n % 30 = 18) (hr5 : r ≠ 5) :
    r % 30 = 19 ∨ r % 30 = 29 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 4 := by
    have : n % 5 = 3 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 4 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_twentyfour {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn24 : n % 30 = 24) (hr5 : r ≠ 5) :
    r % 30 = 7 ∨ r % 30 = 17 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 2 := by
    have : n % 5 = 4 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 2 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma five_ne_sub_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) (hn : 10 < n) : 5 ≠ n - r := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

lemma seven_ne_sub_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) (hn : 14 < n) : 7 ≠ n - r := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

lemma five_not_mem_Sset_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 10 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : 5 ∉ Sset n := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  intro h5
  have : 5 = r ∨ 5 = n - r ∨ 5 = s ∨ 5 = n - s := by
    simpa [hS] using h5
  rcases this with h | h | h | h
  · exact hr5 h.symm
  · exact (five_ne_sub_pairedRep hr hn) h
  · exact hs5 h.symm
  · exact (five_ne_sub_pairedRep hs hn) h

/-- If `n ≡ 6 (mod 30)` and `q ≡ 7 (mod 30)` with `q ≤ 2 * n`, then `5 ∣ 2 * n - q`. -/
lemma five_dvd_two_n_sub_of_mod_six_seven {n q : ℕ} (hn : n % 30 = 6) (hq : q % 30 = 7)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 1 := by omega
    have hq5 : q % 5 = 2 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- If `n ≡ 6 (mod 30)` and `q ≡ 17 (mod 30)` with `q ≤ 2 * n`, then `5 ∣ 2 * n - q`. -/
lemma five_dvd_two_n_sub_of_mod_six_seventeen {n q : ℕ} (hn : n % 30 = 6) (hq : q % 30 = 17)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 1 := by omega
    have hq5 : q % 5 = 2 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- For `n ≡ 6 (mod 30)` a generic `q ≡ 7 (mod 30)` cannot be paired. -/
lemma not_mem_Paired_of_n_mod_six_of_q_mod_seven {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 14 < n) (hn6 : n % 30 = 6) (hq7 : q % 30 = 7)
    (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_six_seven hn6 hq7 (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime :=
    not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    have := (sub_mem_Sset_iff hq).mp hnq
    exact hnp this
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Paired_of_n_mod_six_of_q_mod_seventeen {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn6 : n % 30 = 6) (hq17 : q % 30 = 17)
    (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_six_seventeen hn6 hq17 (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime :=
    not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    have := (sub_mem_Sset_iff hq).mp hnq
    exact hnp this
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)`, nothing of residue `7` is in `Sset`. -/
lemma not_mem_Sset_of_config40_n_mod_six_q_mod_seven {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 14 < n) (hn6 : n % 30 = 6)
    (hU : Unpaired n = ∅) (hq7 : q % 30 = 7) : q ∉ Sset n := by
  intro hq
  have hUmem := not_mem_Paired_of_n_mod_six_of_q_mod_seven h6 hn hn6 hq7 hq
  simp [hU] at hUmem

lemma not_mem_Sset_of_config40_n_mod_six_q_mod_seventeen {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn6 : n % 30 = 6)
    (hU : Unpaired n = ∅) (hq17 : q % 30 = 17) : q ∉ Sset n := by
  intro hq
  have hUmem := not_mem_Paired_of_n_mod_six_of_q_mod_seventeen h6 hn hn6 hq17 hq
  simp [hU] at hUmem

/-- Automatic unpaired residues for the other classes modulo 30. -/
lemma five_dvd_two_n_sub_of_mod_twelve_nineteen {n q : ℕ} (hn : n % 30 = 12) (hq : q % 30 = 19)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 2 := by omega
    have hq5 : q % 5 = 4 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twelve_twenty_nine {n q : ℕ} (hn : n % 30 = 12) (hq : q % 30 = 29)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 2 := by omega
    have hq5 : q % 5 = 4 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_eighteen_one {n q : ℕ} (hn : n % 30 = 18) (hq : q % 30 = 1)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 3 := by omega
    have hq5 : q % 5 = 1 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_eighteen_eleven {n q : ℕ} (hn : n % 30 = 18) (hq : q % 30 = 11)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 3 := by omega
    have hq5 : q % 5 = 1 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twentyfour_thirteen {n q : ℕ} (hn : n % 30 = 24) (hq : q % 30 = 13)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 4 := by omega
    have hq5 : q % 5 = 3 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twentyfour_twenty_three {n q : ℕ} (hn : n % 30 = 24) (hq : q % 30 = 23)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 4 := by omega
    have hq5 : q % 5 = 3 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)` and generic representatives,
every element of `Sset` is `13` or `23` modulo `30`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_six {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 13 ∨ q % 30 = 23 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_six h6 (by omega) hr hn6 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_six h6 (by omega) hs hn6 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 13 ∨ (n - r) % 30 = 23 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 13 ∨ (n - s) % 30 = 23 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_six {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_six h6 hn hn6 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 1 := by omega
  omega

/-- Analogous residue lock for `n ≡ 12 (mod 30)`. -/
lemma five_dvd_two_n_sub_of_mod_twelve_of {n q : ℕ} (hn : n % 30 = 12)
    (hq : q % 30 = 19 ∨ q % 30 = 29) (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  rcases hq with h | h
  · exact five_dvd_two_n_sub_of_mod_twelve_nineteen hn h hle
  · exact five_dvd_two_n_sub_of_mod_twelve_twenty_nine hn h hle

lemma not_mem_Paired_of_n_mod_twelve_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn12 : n % 30 = 12)
    (hqres : q % 30 = 19 ∨ q % 30 = 29) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_twelve_of hn12 hqres (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_twelve_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn12 : n % 30 = 12)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 19 ∨ q % 30 = 29) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_twelve_auto h6 hn hn12 hqres hq
  simp [hU] at this

lemma not_mem_Paired_of_n_mod_eighteen_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn18 : n % 30 = 18)
    (hqres : q % 30 = 1 ∨ q % 30 = 11) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := by
    rcases hqres with h | h
    · exact five_dvd_two_n_sub_of_mod_eighteen_one hn18 h (by omega)
    · exact five_dvd_two_n_sub_of_mod_eighteen_eleven hn18 h (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_eighteen_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn18 : n % 30 = 18)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 1 ∨ q % 30 = 11) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_eighteen_auto h6 hn hn18 hqres hq
  simp [hU] at this

lemma not_mem_Paired_of_n_mod_twentyfour_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn24 : n % 30 = 24)
    (hqres : q % 30 = 13 ∨ q % 30 = 23) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := by
    rcases hqres with h | h
    · exact five_dvd_two_n_sub_of_mod_twentyfour_thirteen hn24 h (by omega)
    · exact five_dvd_two_n_sub_of_mod_twentyfour_twenty_three hn24 h (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_twentyfour_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn24 : n % 30 = 24)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 13 ∨ q % 30 = 23) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_twentyfour_auto h6 hn hn24 hqres hq
  simp [hU] at this

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 12 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_twelve {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn12 : n % 30 = 12)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 1 ∨ q % 30 = 11 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_twelve h6 (by omega) hr hn12 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_twelve h6 (by omega) hs hn12 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 1 ∨ (n - r) % 30 = 11 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 1 ∨ (n - s) % 30 = 11 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_twelve {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn12 : n % 30 = 12)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_twelve h6 hn hn12 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 7 := by omega
  omega

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 18 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_eighteen {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn18 : n % 30 = 18)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 19 ∨ q % 30 = 29 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 (by omega) hr hn18 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 (by omega) hs hn18 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 19 ∨ (n - r) % 30 = 29 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 19 ∨ (n - s) % 30 = 29 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_eighteen {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn18 : n % 30 = 18)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_eighteen h6 hn hn18 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 13 := by omega
  omega

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 24 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_twentyfour {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn24 : n % 30 = 24)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 7 ∨ q % 30 = 17 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 (by omega) hr hn24 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 (by omega) hs hn24 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 7 ∨ (n - r) % 30 = 17 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 7 ∨ (n - s) % 30 = 17 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_twentyfour {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn24 : n % 30 = 24)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_twentyfour h6 hn hn24 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 19 := by omega
  omega

/-- A prime other than `2,3,5` is coprime to `30`, hence one of the eight units mod `30`. -/
lemma prime_mod_thirty_of_gt_five {q : ℕ} (hq : q.Prime) (h5 : 5 < q) :
    q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
    q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 := by
  have h2 : q % 2 = 1 := by
    have : q ≠ 2 := by omega
    exact (hq.eq_two_or_odd).resolve_left this
  have h3 : q % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 3 = q := (prime_dvd_prime_iff_eq prime_three hq).mp hdvd
    omega
  have h5m : q % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 5 = q := (prime_dvd_prime_iff_eq prime_five hq).mp hdvd
    omega
  have hlt : q % 30 < 30 := Nat.mod_lt _ (by decide)
  have hcases : q % 30 = 0 ∨ q % 30 = 1 ∨ q % 30 = 2 ∨ q % 30 = 3 ∨ q % 30 = 4 ∨
      q % 30 = 5 ∨ q % 30 = 6 ∨ q % 30 = 7 ∨ q % 30 = 8 ∨ q % 30 = 9 ∨
      q % 30 = 10 ∨ q % 30 = 11 ∨ q % 30 = 12 ∨ q % 30 = 13 ∨ q % 30 = 14 ∨
      q % 30 = 15 ∨ q % 30 = 16 ∨ q % 30 = 17 ∨ q % 30 = 18 ∨ q % 30 = 19 ∨
      q % 30 = 20 ∨ q % 30 = 21 ∨ q % 30 = 22 ∨ q % 30 = 23 ∨ q % 30 = 24 ∨
      q % 30 = 25 ∨ q % 30 = 26 ∨ q % 30 = 27 ∨ q % 30 = 28 ∨ q % 30 = 29 := by
    omega
  rcases hcases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inl h
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inl h)
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inl h))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- Unpaired elements are never `≡ 13` or `23` *and* paired; this records the
auto-unpaired residues for a generic unpaired element when `n ≡ 6 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_six {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn6 : n % 30 = 6) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 7 ∨ q % 30 = 17 ∨ q % 30 = 13 ∨ q % 30 = 23 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      rcases this with h | h | h | h | h | h | h | h
      · -- `q ≡ 1 (mod 30)` generic is `n - q ≡ 5 (mod 30)`, hence composite unless `q = n - 5`.
        have hnq : (n - q) % 30 = 5 := by
          have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 11 (mod 30)`: `n + q ≡ 17 (mod 30)` is fine, but `n - q ≡ 25 (mod 30)`
        -- is divisible by 5.
        have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hnq : (n - q) % 30 = 17 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        -- `n - q ≡ 17` is allowed as a number, but `n + q ≡ 25 (mod 30)` is div by 5.
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim

/-- Unpaired candidates when `n ≡ 12 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_twelve {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn12 : n % 30 = 12) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 19 ∨ q % 30 = 29 ∨ q % 30 = 1 ∨ q % 30 = 11 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 7`: `n + q ≡ 19` is fine, but `n - q ≡ 5 (mod 30)` is div by 5
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · -- `q ≡ 13`: `n - q ≡ 29`, `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · -- `q ≡ 17`: `n + q ≡ 29`, `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 23`: `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Unpaired candidates when `n ≡ 18 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_eighteen {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn18 : n % 30 = 18) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 1 ∨ q % 30 = 11 ∨ q % 30 = 19 ∨ q % 30 = 29 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 7`: `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · -- `q ≡ 13`: `n - q ≡ 5` div by 5 (unless q = n-5)
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · -- `q ≡ 17`: `n - q ≡ 1`, `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 23`: `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Unpaired candidates when `n ≡ 24 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_twentyfour {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn24 : n % 30 = 24) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 13 ∨ q % 30 = 23 ∨ q % 30 = 7 ∨ q % 30 = 17 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · -- `q ≡ 1`: `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 11`: `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · -- `q ≡ 19`: `n - q ≡ 5` div by 5 (unless q = n-5)
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · -- `q ≡ 29`: `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim

/-- In a `(4,0)` configuration every Sset element is one of the two pairing orbits. -/
lemma mem_Sset_of_config40 {n r s q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hq : q ∈ Sset n) : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
  have hS := Sset_eq_four_of_config40 h6 hn hP hU hr hs hrs
  simpa [hS] using hq

/-- A paired representative is strictly less than `n / 2`. -/
lemma pairedRep_mul_two_lt {n r : ℕ} (hr : r ∈ PairedRep n) : 2 * r < n := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

/-- If `q ∈ Sset n` and `2 * q < n` in a `(4,0)` configuration, then `q` is a pairing representative. -/
lemma eq_pairedRep_of_mem_Sset_of_mul_two_lt {n r s q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hq : q ∈ Sset n) (h2q : 2 * q < n) : q = r ∨ q = s := by
  have hmem := mem_Sset_of_config40 h6 hn hP hU hr hs hrs hq
  have hr2 := pairedRep_mul_two_lt hr
  have hs2 := pairedRep_mul_two_lt hs
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  rcases hmem with h | h | h | h
  · exact Or.inl h
  · omega
  · exact Or.inr h
  · omega

/-- For `n > 26` in a `(4,0)` configuration, `13 ∈ Sset n` iff `13` is a pairing representative. -/
lemma thirteen_mem_Sset_iff_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 26 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    13 ∈ Sset n ↔ r = 13 ∨ s = 13 := by
  constructor
  · intro h13
    have : 2 * 13 < n := by omega
    have := eq_pairedRep_of_mem_Sset_of_mul_two_lt h6 (by omega) hP hU hr hs hrs h13 this
    rcases this with h | h <;> simp [h]
  · intro h
    have hrS := pairedRep_mem_Sset hr
    have hsS := pairedRep_mem_Sset hs
    rcases h with h | h
    · subst h; exact hrS
    · subst h; exact hsS

lemma twentythree_mem_Sset_iff_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 46 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    23 ∈ Sset n ↔ r = 23 ∨ s = 23 := by
  constructor
  · intro h23
    have : 2 * 23 < n := by omega
    have := eq_pairedRep_of_mem_Sset_of_mul_two_lt h6 (by omega) hP hU hr hs hrs h23 this
    rcases this with h | h <;> simp [h]
  · intro h
    have hrS := pairedRep_mem_Sset hr
    have hsS := pairedRep_mem_Sset hs
    rcases h with h | h
    · subst h; exact hrS
    · subst h; exact hsS

/-- Residues of pairing representatives and their partners when `n ≡ 6 (mod 30)`
and the representatives are not `5`. -/
lemma eight_residues_n_mod_six {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hn6 : n % 30 = 6) (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    (r % 30 = 13 ∨ r % 30 = 23) ∧ (s % 30 = 13 ∨ s % 30 = 23) ∧
    (n - r) % 30 = (36 - r % 30) % 30 ∧ (n + r) % 30 = (6 + r % 30) % 30 := by
  have hr30 := pairedRep_mod_thirty_of_n_mod_six h6 hn hr hn6 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_six h6 hn hs hn6 hs5
  have hrlt := pairedRep_lt_n hr
  refine ⟨hr30, hs30, ?_, ?_⟩
  · have hnr : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rw [hnr, hn6]
  · omega

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)` and representatives not `5`,
every Sset element is congruent to `13` or `23` modulo `30`. -/
lemma sset_mod_thirty_subset_of_config40_n_mod_six {n r s q : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 13 ∨ q % 30 = 23 :=
  mem_Sset_mod_thirty_of_config40_n_mod_six h6 hn hn6 hP hU hr hs hrs hr5 hs5 hq

/-- The two pairing representatives in a `(4,0)` configuration with `n ≡ 6 (mod 30)`
are each `13` or `23` modulo `30`. -/
lemma reps_mod_thirty_of_config40_n_mod_six {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn6 : n % 30 = 6)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    (r % 30 = 13 ∨ r % 30 = 23) ∧ (s % 30 = 13 ∨ s % 30 = 23) :=
  ⟨pairedRep_mod_thirty_of_n_mod_six h6 hn hr hn6 hr5,
   pairedRep_mod_thirty_of_n_mod_six h6 hn hs hn6 hs5⟩

/-- If the two pairing representatives are `13` and `23`, the eight diamond values
are the explicit linear forms in `n` attached to those two primes. -/
lemma eight_primes_of_reps_thirteen_twentythree {n r s : ℕ}
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hrs13 : ({r, s} : Finset ℕ) = {13, 23}) :
    (13 : ℕ).Prime ∧ (23 : ℕ).Prime ∧
    (n - 13).Prime ∧ (n - 23).Prime ∧
    (n + 13).Prime ∧ (n + 23).Prime ∧
    (2 * n - 13).Prime ∧ (2 * n - 23).Prime := by
  have h13 : 13 ∈ ({r, s} : Finset ℕ) := by simp [hrs13]
  have h23 : 23 ∈ ({r, s} : Finset ℕ) := by simp [hrs13]
  have hr13or : r = 13 ∨ s = 13 := by
    simp only [mem_insert, mem_singleton] at h13
    exact h13.imp Eq.symm Eq.symm
  have hr23or : r = 23 ∨ s = 23 := by
    simp only [mem_insert, mem_singleton] at h23
    exact h23.imp Eq.symm Eq.symm
  have ⟨hrp, hnrp, hnpr, h2nr, hsp, hnsp, hnsp', h2ns⟩ := eight_primes_of_two_reps hr hs
  rcases hr13or with hr13 | hs13 <;> rcases hr23or with hr23 | hs23
  · have : (13 : ℕ) = 23 := hr13.symm.trans hr23
    exact (by decide : ¬ (13 : ℕ) = 23) this |>.elim
  · subst hr13; subst hs23
    exact ⟨by decide, by decide, hnrp, hnsp, hnpr, hnsp', h2nr, h2ns⟩
  · subst hs13; subst hr23
    exact ⟨by decide, by decide, hnsp, hnrp, hnsp', hnpr, h2ns, h2nr⟩
  · have : (23 : ℕ) = 13 := hs23.symm.trans hs13
    exact (by decide : ¬ (23 : ℕ) = 13) this |>.elim

/-- A pairing representative other than `5` is at least `7`. -/
lemma seven_le_pairedRep_of_ne_five {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hr5 : r ≠ 5) : 7 ≤ r := by
  have hS := pairedRep_mem_Sset hr
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn hS
  have hrP : r.Prime := (mem_Sset_iff.mp hS).2.1
  have hr2 : r ≠ 2 := by omega
  have hodd : Odd r := hrP.odd_of_ne_two hr2
  have : r ≠ 6 := fun h => by
    subst h
    exact (by decide : ¬ Odd 6) hodd
  omega

/-- If both `5` and `n - 5` lie in `Sset n` then they form a pairing orbit. -/
lemma five_and_nsubfive_paired {n : ℕ} (hn : 10 < n)
    (h5 : 5 ∈ Sset n) (hn5 : n - 5 ∈ Sset n) :
    5 ∈ Paired n ∧ n - 5 ∈ Paired n := by
  have hle : 5 ≤ n := by omega
  refine ⟨mem_Paired_iff.mpr ⟨h5, hn5⟩, mem_Paired_iff.mpr ⟨hn5, ?_⟩⟩
  simpa [Nat.sub_sub_self hle] using h5

/-- In an all-unpaired configuration, at most one of `5` and `n - 5` can lie in `Sset`. -/
lemma not_both_five_of_unpaired_empty_paired {n : ℕ} (hn : 10 < n)
    (hP : Paired n = ∅) : ¬ (5 ∈ Sset n ∧ n - 5 ∈ Sset n) := by
  intro ⟨h5, hn5⟩
  have := five_and_nsubfive_paired hn h5 hn5
  have : 5 ∈ Paired n := this.1
  simp [hP] at this

/-- If `7, 13, 17, 23` all lie in `Sset n` then one of `n ± 7, n ± 13, n ± 17, n ± 23`
is divisible by `7`. For `n > 46` that number exceeds `7`, hence cannot be prime. -/
lemma not_all_seven_thirteen_seventeen_twentythree_mem_Sset {n : ℕ} (hn : 46 < n) :
    ¬ (7 ∈ Sset n ∧ 13 ∈ Sset n ∧ 17 ∈ Sset n ∧ 23 ∈ Sset n) := by
  intro ⟨h7, h13, h17, h23⟩
  have hsum7 : (n + 7).Prime := (mem_Sset_iff.mp h7).2.2.2
  have hsum13 : (n + 13).Prime := (mem_Sset_iff.mp h13).2.2.2
  have hdiff13 : (n - 13).Prime := (mem_Sset_iff.mp h13).2.2.1
  have hsum17 : (n + 17).Prime := (mem_Sset_iff.mp h17).2.2.2
  have hdiff17 : (n - 17).Prime := (mem_Sset_iff.mp h17).2.2.1
  have hsum23 : (n + 23).Prime := (mem_Sset_iff.mp h23).2.2.2
  have hdiff23 : (n - 23).Prime := (mem_Sset_iff.mp h23).2.2.1
  have hmod : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨
      n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  have hadd (t : ℕ) : (n + t) % 7 = (n % 7 + t % 7) % 7 := Nat.add_mod n t 7
  have hsub (t : ℕ) (ht : t ≤ n) : (n - t) % 7 = (n % 7 + 7 - t % 7) % 7 := by
    have := Nat.mod_add_div n 7
    have := Nat.mod_add_div t 7
    omega
  rcases hmod with h | h | h | h | h | h | h
  · have : (n + 7) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum7
  · have : (n + 13) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum13
  · have : (n - 23) % 7 = 0 := by rw [hsub 23 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff23
  · have : (n - 17) % 7 = 0 := by rw [hsub 17 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff17
  · have : (n + 17) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum17
  · have : (n + 23) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum23
  · have : (n - 13) % 7 = 0 := by rw [hsub 13 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff13

lemma nat_sub_mod_eq_zero_of {n q p : ℕ} (hp : 0 < p) (hle : q ≤ n)
    (hminus : (n % p + p - q % p) % p = 0) :
    (n - q) % p = 0 := by
  have hZ : ((n - q : ℕ) : ℤ) = (n : ℤ) - q := Int.ofNat_sub hle
  have hsub : ((n : ℤ) - q) % p = ((n : ℤ) % p - (q : ℤ) % p) % p := Int.sub_emod _ _ _
  have hnmod : ((n : ℤ) % p) = ↑(n % p) := Int.natCast_mod n p
  have hqmod : ((q : ℤ) % p) = ↑(q % p) := Int.natCast_mod q p
  have haddP : ((n : ℤ) % p - (q : ℤ) % p) % p =
      ((n : ℤ) % p + ↑p - (q : ℤ) % p) % p := by
    have : ((n : ℤ) % p + ↑p - (q : ℤ) % p) =
        ((n : ℤ) % p - (q : ℤ) % p) + ↑p := by
      simp [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm]
    rw [this, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  have hminusZ : ((↑(n % p) : ℤ) + ↑p - ↑(q % p)) % p = 0 := by
    have : ((↑(n % p) : ℤ) + ↑p - ↑(q % p)) = ↑(n % p + p - q % p) := by
      have hle' : q % p ≤ n % p + p := by
        have : q % p < p := Nat.mod_lt _ hp
        omega
      rw [Nat.cast_sub hle', Nat.cast_add]
    rw [this]
    exact_mod_cast hminus
  have : ((n : ℤ) - q) % p = 0 := by
    rw [hsub, haddP, hnmod, hqmod]
    exact hminusZ
  have : ((n - q : ℕ) : ℤ) % p = 0 := by rwa [hZ]
  exact_mod_cast this

/-- If a finite set of offsets covers every residue class modulo a prime `p`,
then those offsets cannot all lie in `Sset n` once `n` is larger than `p` plus
every offset (so that each `n ± q` exceeds `p`). -/
lemma not_all_mem_Sset_of_mod_cover {n p : ℕ} {qs : Finset ℕ}
    (hp : p.Prime)
    (hn : ∀ q ∈ qs, q + p < n)
    (hcover : ∀ r < p, ∃ q ∈ qs, (r + q) % p = 0 ∨ (r + p - q % p) % p = 0) :
    ¬ qs ⊆ Sset n := by
  intro hsub
  have hppos : 0 < p := hp.pos
  have hmod : n % p < p := Nat.mod_lt _ hppos
  obtain ⟨q, hq, hhit⟩ := hcover (n % p) hmod
  have hqS : q ∈ Sset n := hsub hq
  have hqlt : q < n := (mem_Sset_iff.mp hqS).1
  have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
  have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
  have hqp : q + p < n := hn q hq
  rcases hhit with hplus | hminus
  · have : (n + q) % p = 0 := by
      have hadd : (n + q) % p = (n % p + q) % p := by
        simpa [Nat.add_mod] using (Nat.add_mod n q p).symm
      simpa [hadd] using hplus
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) hp.two_le
      (by omega) hsumP
  · have : (n - q) % p = 0 :=
      nat_sub_mod_eq_zero_of hppos (Nat.le_of_lt hqlt) hminus
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) hp.two_le
      (by omega) hdiffP



lemma zmod7_two_ne_zero : (2 : ZMod 7) ≠ 0 := by decide

lemma two_n_ne_zero_mod_seven {n : ZMod 7} (hn : n ≠ 0) : (2 : ZMod 7) * n ≠ 0 := by
  fin_cases n <;> first | exact (hn rfl).elim | decide

lemma n_ne_neg_n_mod_seven {n : ZMod 7} (hn : n ≠ 0) : n ≠ -n := by
  intro h
  apply two_n_ne_zero_mod_seven hn
  have := congrArg (fun x => x + n) h
  simpa [two_mul] using this

lemma card_pair_zmod7 {a b : ZMod 7} (h : a ≠ b) : #({a, b} : Finset (ZMod 7)) = 2 := by
  rw [card_insert_of_notMem, card_singleton]
  simpa using h

lemma card_triple_zmod7 {a b c : ZMod 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #({a, b, c} : Finset (ZMod 7)) = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simpa using hbc
  · simp [hab, hac]

lemma card_quad_zmod7 {a b c d : ZMod 7}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    #({a, b, c, d} : Finset (ZMod 7)) = 4 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simpa using hcd
  · simp [hbc, hbd]
  · simp [hab, hac, had]

lemma sum_univ_zmod7 : (∑ x : ZMod 7, x) = 0 := by decide

lemma sum_forbidden_zmod7 (n : ZMod 7) : (∑ x ∈ ({0, n, -n} : Finset (ZMod 7)), x) = 0 := by
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases hnn : n = -n
    · have := n_ne_neg_n_mod_seven h0 hnn
      contradiction
    · rw [sum_insert, sum_insert, sum_singleton]
      · ring
      · simpa using hnn
      · simpa [Ne.symm h0] using h0

/-- If four distinct residues avoid `{0, n, -n}` in `ZMod 7` (with `n ≠ 0`),
they occupy the whole complement and therefore sum to `0`. -/
lemma four_allowed_residues_sum_zero
    (n a b c d : ZMod 7)
    (hn : n ≠ 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (han : a ≠ n) (hbn : b ≠ n) (hcn : c ≠ n) (hdn : d ≠ n)
    (hann : a ≠ -n) (hbnn : b ≠ -n) (hcnn : c ≠ -n) (hdnn : d ≠ -n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    a + b + c + d = 0 := by
  let S : Finset (ZMod 7) := {a, b, c, d}
  let F : Finset (ZMod 7) := {0, n, -n}
  have hFn : n ≠ -n := n_ne_neg_n_mod_seven hn
  have hF0n : (0 : ZMod 7) ≠ n := by intro h; exact hn h.symm
  have hF0nn : (0 : ZMod 7) ≠ -n := by
    intro h
    have : n = 0 := neg_eq_zero.mp h.symm
    exact hn this
  have hcardF : #F = 3 := card_triple_zmod7 hF0n hF0nn hFn
  have hcardS : #S = 4 := card_quad_zmod7 hab hac had hbc hbd hcd
  have hcard_compl : #(univ \ F) = 4 := by
    rw [card_sdiff_of_subset (subset_univ _), hcardF]
    have : #(univ : Finset (ZMod 7)) = 7 := by decide
    omega
  have hsub : S ⊆ univ \ F := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and]
    intro hF
    simp only [F, mem_insert, mem_singleton] at hF
    simp only [S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hF with rfl | rfl | rfl <;> contradiction
  have hSF : S = univ \ F :=
    eq_of_subset_of_card_le hsub (by simp [hcardS, hcard_compl])
  have hsumS : (∑ x ∈ S, x) = a + b + c + d := by
    simp only [S]
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · ring
    · simp [hcd]
    · simp [hbc, hbd]
    · simp [hab, hac, had]
  have hsum_compl : (∑ x ∈ univ \ F, x) = 0 := by
    have hss : (∑ x ∈ (univ : Finset (ZMod 7)) \ F, x) =
        (∑ x ∈ univ, x) - ∑ x ∈ F, x :=
      sum_sdiff_eq_sub (subset_univ F)
    rw [hss, sum_univ_zmod7, sum_forbidden_zmod7 n, sub_zero]
  rw [← hsumS, hSF, hsum_compl]

lemma two_diamonds_cast_sub {n r : ℕ} (hrle : r ≤ n) :
    ((n - r : ℕ) : ZMod 7) = (n : ZMod 7) - r :=
  Nat.cast_sub hrle

lemma two_diamonds_sum_eq_two_n {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n) :
    (r : ZMod 7) + ((n - r : ℕ) : ZMod 7) +
      (s : ZMod 7) + ((n - s : ℕ) : ZMod 7) = (2 : ZMod 7) * n := by
  rw [two_diamonds_cast_sub hrle, two_diamonds_cast_sub hsle]
  ring

/-- Two pairing orbits cannot occupy four distinct allowed residues modulo 7. -/
lemma two_diamonds_residues_not_all_distinct_mod_seven
    {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n)
    (hn7 : (n : ZMod 7) ≠ 0)
    (hr0 : (r : ZMod 7) ≠ 0) (hs0 : (s : ZMod 7) ≠ 0)
    (hrn : (r : ZMod 7) ≠ n) (hsn : (s : ZMod 7) ≠ n)
    (hrnn : (r : ZMod 7) ≠ -n) (hsnn : (s : ZMod 7) ≠ -n)
    (hnr0 : ((n - r : ℕ) : ZMod 7) ≠ 0) (hns0 : ((n - s : ℕ) : ZMod 7) ≠ 0)
    (hnrn : ((n - r : ℕ) : ZMod 7) ≠ n) (hnsn : ((n - s : ℕ) : ZMod 7) ≠ n)
    (hnrnn : ((n - r : ℕ) : ZMod 7) ≠ -n) (hnsnn : ((n - s : ℕ) : ZMod 7) ≠ -n)
    (hrs : (r : ZMod 7) ≠ s)
    (hrns : (r : ZMod 7) ≠ (n - s : ℕ))
    (hrnr : (r : ZMod 7) ≠ (n - r : ℕ))
    (hsns : (s : ZMod 7) ≠ (n - s : ℕ))
    (hnrns : ((n - r : ℕ) : ZMod 7) ≠ (n - s : ℕ))
    (hnrs : ((n - r : ℕ) : ZMod 7) ≠ s) :
    False := by
  have hsum0 := four_allowed_residues_sum_zero (n : ZMod 7)
    (r : ZMod 7) ((n - r : ℕ) : ZMod 7) (s : ZMod 7) ((n - s : ℕ) : ZMod 7)
    hn7 hr0 hnr0 hs0 hns0
    hrn hnrn hsn hnsn
    hrnn hnrnn hsnn hnsnn
    hrnr hrs hrns hnrs hnrns hsns
  have hsum2 := two_diamonds_sum_eq_two_n hrle hsle
  have h2n := two_n_ne_zero_mod_seven hn7
  exact h2n (hsum2 ▸ hsum0)

lemma natCast_zmod7_ne_zero {m : ℕ} (h : ¬ 7 ∣ m) : (m : ZMod 7) ≠ 0 := by
  intro h0
  exact h ((ZMod.natCast_eq_zero_iff m 7).mp h0)

lemma prime_ne_seven_cast {p : ℕ} (hp : p.Prime) (h7 : p ≠ 7) : (p : ZMod 7) ≠ 0 := by
  intro h0
  have : 7 ∣ p := (ZMod.natCast_eq_zero_iff p 7).mp h0
  have : 7 = p := (prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp this
  exact h7 this.symm

/-- A pairing representative is at most `n/2`, so for `n > 14` it cannot be `n - 7`. -/
lemma pairedRep_ne_n_sub_seven {n r : ℕ} (hr : r ∈ PairedRep n) (hn : 14 < n) :
    n - r ≠ 7 := by
  have hlt := pairedRep_lt_half hr
  intro h
  omega

lemma pairedRep_ne_seven_of_not_mem {n r : ℕ}
    (hr : r ∈ PairedRep n) (h7 : 7 ∉ Sset n) : r ≠ 7 := by
  intro h; subst h
  exact h7 (pairedRep_mem_Sset hr)

/-- Two pairing representatives, with `7` dividing neither `n` nor either
representative, must collide modulo `7`: their four orbit residues cannot be
distinct. -/
lemma diamonds_collide_mod_seven
    {n r s : ℕ} (hrle : r ≤ n) (hsle : s ≤ n)
    (hn7 : ¬ 7 ∣ n)
    (hrP : r.Prime) (hsP : s.Prime)
    (hnrP : (n - r).Prime) (hnsP : (n - s).Prime)
    (hsumrP : (n + r).Prime) (hsumsP : (n + s).Prime)
    (h2nrP : (2 * n - r).Prime) (h2nsP : (2 * n - s).Prime)
    (hrne7 : r ≠ 7) (hsne7 : s ≠ 7)
    (hnrne7 : n - r ≠ 7) (hnsne7 : n - s ≠ 7)
    (hsumrne7 : n + r ≠ 7) (hsumsne7 : n + s ≠ 7)
    (h2nrne7 : 2 * n - r ≠ 7) (h2nsne7 : 2 * n - s ≠ 7) :
    (r : ZMod 7) = s ∨ (r : ZMod 7) = ((n - s : ℕ) : ZMod 7) ∨
    (r : ZMod 7) = ((n - r : ℕ) : ZMod 7) ∨
    (s : ZMod 7) = ((n - s : ℕ) : ZMod 7) := by
  have hn7Z := natCast_zmod7_ne_zero hn7
  have not7 {p : ℕ} (hp : p.Prime) (hne7 : p ≠ 7) : (p : ZMod 7) ≠ 0 := by
    intro h0
    have : 7 ∣ p := (ZMod.natCast_eq_zero_iff p 7).mp h0
    have heq : 7 = p :=
      (prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hp).mp this
    exact hne7 heq.symm
  have hr0 := not7 hrP hrne7
  have hs0 := not7 hsP hsne7
  have hnr0 := not7 hnrP hnrne7
  have hns0 := not7 hnsP hnsne7
  have hrn : (r : ZMod 7) ≠ n := by
    intro h
    apply hnr0
    rw [Nat.cast_sub hrle, h, sub_self]
  have hsn : (s : ZMod 7) ≠ n := by
    intro h
    apply hns0
    rw [Nat.cast_sub hsle, h, sub_self]
  have hrnn : (r : ZMod 7) ≠ -n := by
    intro h
    have : ((n + r : ℕ) : ZMod 7) = 0 := by push_cast; simp [h]
    exact not7 hsumrP hsumrne7 this
  have hsnn : (s : ZMod 7) ≠ -n := by
    intro h
    have : ((n + s : ℕ) : ZMod 7) = 0 := by push_cast; simp [h]
    exact not7 hsumsP hsumsne7 this
  have hnrn : ((n - r : ℕ) : ZMod 7) ≠ n := by
    intro h
    apply hr0
    have h' : (n : ZMod 7) - ((n - r : ℕ) : ZMod 7) = 0 := by rw [h, sub_self]
    rw [Nat.cast_sub hrle] at h'
    -- n - (n - r) = r
    simpa using h'
  have hnsn : ((n - s : ℕ) : ZMod 7) ≠ n := by
    intro h
    apply hs0
    have h' : (n : ZMod 7) - ((n - s : ℕ) : ZMod 7) = 0 := by rw [h, sub_self]
    rw [Nat.cast_sub hsle] at h'
    simpa using h'
  have h2rle : r ≤ 2 * n := by omega
  have h2sle : s ≤ 2 * n := by omega
  have hnrnn : ((n - r : ℕ) : ZMod 7) ≠ -n := by
    intro h
    have hcast : ((2 * n - r : ℕ) : ZMod 7) =
        (n : ZMod 7) + ((n - r : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub h2rle, Nat.cast_sub hrle, Nat.cast_mul, Nat.cast_two]
      simp [sub_eq_add_neg, two_mul]; ac_rfl
    have : ((2 * n - r : ℕ) : ZMod 7) = 0 := by
      rw [hcast, h]; abel
    exact not7 h2nrP h2nrne7 this
  have hnsnn : ((n - s : ℕ) : ZMod 7) ≠ -n := by
    intro h
    have hcast : ((2 * n - s : ℕ) : ZMod 7) =
        (n : ZMod 7) + ((n - s : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub h2sle, Nat.cast_sub hsle, Nat.cast_mul, Nat.cast_two]
      simp [sub_eq_add_neg, two_mul]; ac_rfl
    have : ((2 * n - s : ℕ) : ZMod 7) = 0 := by
      rw [hcast, h]; abel
    exact not7 h2nsP h2nsne7 this
  by_contra hnone
  simp only [not_or] at hnone
  obtain ⟨hrs, hrns, hrnr, hsns⟩ := hnone
  have hnrns : ((n - r : ℕ) : ZMod 7) ≠ (n - s : ℕ) := by
    intro h
    apply hrs
    rw [Nat.cast_sub hrle, Nat.cast_sub hsle] at h
    -- n-r = n-s ⇒ r = s
    have : -(r : ZMod 7) = -s := by
      simpa using h
    exact neg_injective this
  have hnrs : ((n - r : ℕ) : ZMod 7) ≠ s := by
    intro h
    apply hrns
    rw [Nat.cast_sub hrle] at h
    rw [Nat.cast_sub hsle]
    apply eq_sub_of_add_eq
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp h).symm
  exact two_diamonds_residues_not_all_distinct_mod_seven hrle hsle hn7Z
    hr0 hs0 hrn hsn hrnn hsnn hnr0 hns0 hnrn hnsn hnrnn hnsnn
    hrs hrns hrnr hsns hnrns hnrs


lemma pairedReps_collide_mod_seven
    {n r s : ℕ} (hn : 46 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hn7 : ¬ 7 ∣ n) (hr7 : r ≠ 7) (hs7 : s ≠ 7) :
    (r : ZMod 7) = s ∨ (r : ZMod 7) = ((n - s : ℕ) : ZMod 7) ∨
    (r : ZMod 7) = ((n - r : ℕ) : ZMod 7) ∨
    (s : ZMod 7) = ((n - s : ℕ) : ZMod 7) := by
  obtain ⟨hrp, hnrp, hnpr, h2nr, hsp, hnsp, hnsp', h2ns⟩ := eight_primes_of_two_reps hr hs
  have hrle : r ≤ n := Nat.le_of_lt (pairedRep_lt_n hr)
  have hsle : s ≤ n := Nat.le_of_lt (pairedRep_lt_n hs)
  have hnr7 : n - r ≠ 7 := pairedRep_ne_n_sub_seven hr (by omega)
  have hns7 : n - s ≠ 7 := pairedRep_ne_n_sub_seven hs (by omega)
  have hsumr7 : n + r ≠ 7 := by
    have : 0 < r := hrp.pos
    omega
  have hsums7 : n + s ≠ 7 := by
    have : 0 < s := hsp.pos
    omega
  have h2nr7 : 2 * n - r ≠ 7 := by
    have h2 := pairedRep_mul_two_lt hr
    omega
  have h2ns7 : 2 * n - s ≠ 7 := by
    have h2 := pairedRep_mul_two_lt hs
    omega
  exact diamonds_collide_mod_seven hrle hsle hn7 hrp hsp hnrp hnsp hnpr hnsp' h2nr h2ns
    hr7 hs7 hnr7 hns7 hsumr7 hsums7 h2nr7 h2ns7

lemma a_ne_four_of_dvd_six_of_gt_8000 {n : ℕ} (h6 : 6 ∣ n) (hgt : 8000 < n) : a n ≠ 4 := by
  intro ha
  have hn6 : 6 < n := by omega
  rcases a_eq_four_config h6 hn6 ha with h40 | h22 | h04
  · obtain ⟨r, s, hr, hs, hrs⟩ := exists_two_pairedReps h6 hn6 h40.1
    obtain ⟨hrp, hnrp, hnrp', h2nr, hsp, hnsp, hnsp', h2ns⟩ := eight_primes_of_two_reps hr hs
    have hU0 : #(Unpaired n) = 0 := h40.2
    have hUempty : Unpaired n = ∅ := card_eq_zero.mp hU0
    have hS : Sset n = {r, n - r, s, n - s} :=
      Sset_eq_four_of_config40 h6 hn6 h40.1 hUempty hr hs hrs
    by_cases hn5 : 5 ∣ n
    · -- `30 ∣ n`: both diamonds live in the eight coprime classes mod 30.
      sorry
    · by_cases hr5 : r = 5
      · sorry
      · by_cases hs5 : s = 5
        · sorry
        · have hcong := two_pairedReps_congruent_mod_five h6 hn6 hr hs hn5 hr5 hs5
          rcases mod_thirty_of_dvd_six_of_not_dvd_five h6 hn5 with h30 | h30 | h30 | h30
          · have hr30 := pairedRep_mod_thirty_of_n_mod_six h6 hn6 hr h30 hr5
            have hs30 := pairedRep_mod_thirty_of_n_mod_six h6 hn6 hs h30 hs5
            -- `n ≡ 6 (mod 30)`, representatives in `{13,23}`.
            have h5out := five_not_mem_Sset_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs hr5 hs5
            have hn5out := n_sub_five_not_mem_Sset_of_config40_n_mod_six
              h6 (by omega) h30 h40.1 hUempty hr hs hrs hr5 hs5
            have h7out : 7 ∉ Sset n :=
              not_mem_Sset_of_config40_n_mod_six_q_mod_seven h6 (by omega) h30 hUempty (by decide)
            have h17out : 17 ∉ Sset n :=
              not_mem_Sset_of_config40_n_mod_six_q_mod_seventeen h6 (by omega) h30 hUempty (by decide)
            have h13iff := thirteen_mem_Sset_iff_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs
            have h23iff := twentythree_mem_Sset_iff_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs
            -- Four subcases according to whether `13` and/or `23` are representatives.
            by_cases h13r : r = 13 ∨ s = 13
            · by_cases h23r : r = 23 ∨ s = 23
              · -- Both `13` and `23` are pairing representatives: `{r, s} = {13, 23}`.
                have hrs13 : ({r, s} : Finset ℕ) = {13, 23} := by
                  apply Finset.Subset.antisymm_iff.mpr
                  constructor
                  · intro x hx
                    simp only [mem_insert, mem_singleton] at hx ⊢
                    rcases hx with rfl | rfl
                    · rcases h13r with h | h <;> rcases h23r with h' | h' <;> omega
                    · rcases h13r with h | h <;> rcases h23r with h' | h' <;> omega
                  · intro x hx
                    simp only [mem_insert, mem_singleton] at hx ⊢
                    rcases hx with rfl | rfl
                    · exact h13r.imp Eq.symm Eq.symm
                    · exact h23r.imp Eq.symm Eq.symm
                -- The eight diamond values are `13, 23, n-23, n-13, n+13, n+23, 2n-23, 2n-13`.
                sorry
              · -- `13` is a representative, `23` is not, hence `23 ∉ Sset n`.
                have h23out : 23 ∉ Sset n := fun h => h23r (h23iff.mp h)
                sorry
            · by_cases h23r : r = 23 ∨ s = 23
              · -- `23` is a representative, `13` is not, hence `13 ∉ Sset n`.
                have h13out : 13 ∉ Sset n := fun h => h13r (h13iff.mp h)
                sorry
              · -- Neither `13` nor `23` is a representative.
                have h13out : 13 ∉ Sset n := fun h => h13r (h13iff.mp h)
                have h23out : 23 ∉ Sset n := fun h => h23r (h23iff.mp h)
                sorry
          · have hr30 := pairedRep_mod_thirty_of_n_mod_twelve h6 hn6 hr h30 hr5
            have hs30 := pairedRep_mod_thirty_of_n_mod_twelve h6 hn6 hs h30 hs5
            have h5out := five_not_mem_Sset_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs hr5 hs5
            have hn5out := n_sub_five_not_mem_Sset_of_config40_n_mod_twelve
              h6 (by omega) h30 h40.1 hUempty hr hs hrs hr5 hs5
            have h19out : ∀ q, q % 30 = 19 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_twelve_auto h6 (by omega) h30 hUempty (Or.inl hq)
            have h29out : ∀ q, q % 30 = 29 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_twelve_auto h6 (by omega) h30 hUempty (Or.inr hq)
            sorry
          · have hr30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 hn6 hr h30 hr5
            have hs30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 hn6 hs h30 hs5
            have h5out := five_not_mem_Sset_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs hr5 hs5
            have hn5out := n_sub_five_not_mem_Sset_of_config40_n_mod_eighteen
              h6 (by omega) h30 h40.1 hUempty hr hs hrs hr5 hs5
            have h1out : ∀ q, q % 30 = 1 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_eighteen_auto h6 (by omega) h30 hUempty (Or.inl hq)
            have h11out : ∀ q, q % 30 = 11 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_eighteen_auto h6 (by omega) h30 hUempty (Or.inr hq)
            sorry
          · have hr30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 hn6 hr h30 hr5
            have hs30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 hn6 hs h30 hs5
            have h5out := five_not_mem_Sset_of_config40 h6 (by omega) h40.1 hUempty hr hs hrs hr5 hs5
            have hn5out := n_sub_five_not_mem_Sset_of_config40_n_mod_twentyfour
              h6 (by omega) h30 h40.1 hUempty hr hs hrs hr5 hs5
            have h13out : ∀ q, q % 30 = 13 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_twentyfour_auto h6 (by omega) h30 hUempty (Or.inl hq)
            have h23out : ∀ q, q % 30 = 23 → q ∉ Sset n := fun q hq =>
              not_mem_Sset_of_config40_n_mod_twentyfour_auto h6 (by omega) h30 hUempty (Or.inr hq)
            sorry
  · -- One pairing orbit and two unpaired elements.
    have hP2 : #(Paired n) = 2 := h22.1
    have hU2 : #(Unpaired n) = 2 := h22.2
    have hR1 : #(PairedRep n) = 1 := pairedRep_card_one_of_paired_two h6 hn6 hP2
    have hUne : (Unpaired n).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      simp [h] at hU2
    obtain ⟨u, hu⟩ := hUne
    have hUrest : (Unpaired n).erase u ≠ ∅ := by
      intro h
      have := card_erase_of_mem hu
      simp [hU2] at this
      simp [h] at this
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hUrest
    have hvU : v ∈ Unpaired n := mem_of_mem_erase hv
    have huv : u ≠ v := (ne_of_mem_erase hv).symm
    by_cases hn5 : 5 ∣ n
    · -- `30 ∣ n`: no auto-unpaired residues.
      sorry
    · rcases mod_thirty_of_dvd_six_of_not_dvd_five h6 hn5 with h30 | h30 | h30 | h30
      · have hu30 := unpaired_mod_thirty_candidates_n_mod_six h6 hn6 h30 hu
        have hv30 := unpaired_mod_thirty_candidates_n_mod_six h6 hn6 h30 hvU
        sorry
      · have hu30 := unpaired_mod_thirty_candidates_n_mod_twelve h6 hn6 h30 hu
        have hv30 := unpaired_mod_thirty_candidates_n_mod_twelve h6 hn6 h30 hvU
        sorry
      · have hu30 := unpaired_mod_thirty_candidates_n_mod_eighteen h6 hn6 h30 hu
        have hv30 := unpaired_mod_thirty_candidates_n_mod_eighteen h6 hn6 h30 hvU
        sorry
      · have hu30 := unpaired_mod_thirty_candidates_n_mod_twentyfour h6 hn6 h30 hu
        have hv30 := unpaired_mod_thirty_candidates_n_mod_twentyfour h6 hn6 h30 hvU
        sorry
  · -- Four unpaired elements.
    have hP0 : #(Paired n) = 0 := h04.1
    have hU4 : #(Unpaired n) = 4 := h04.2
    have hR0 : #(PairedRep n) = 0 := pairedRep_card_zero_of_paired_zero h6 hn6 hP0
    have hUeq : Unpaired n = Sset n := by
      have := paired_union_unpaired n
      have hPempty : Paired n = ∅ := card_eq_zero.mp hP0
      simpa [hPempty] using this
    by_cases hn5 : 5 ∣ n
    · sorry
    · rcases mod_thirty_of_dvd_six_of_not_dvd_five h6 hn5 with h30 | h30 | h30 | h30
      · sorry
      · sorry
      · sorry
      · sorry

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  rintro ⟨n, hn⟩
  by_cases h6 : 6 ∣ n
  · by_cases hle : n ≤ 8000
    · exact a_ne_four_of_dvd_six_of_le_8000 h6 hle hn
    · exact a_ne_four_of_dvd_six_of_gt_8000 h6 (by omega) hn
  · exact a_ne_four_of_not_dvd_six h6 hn
