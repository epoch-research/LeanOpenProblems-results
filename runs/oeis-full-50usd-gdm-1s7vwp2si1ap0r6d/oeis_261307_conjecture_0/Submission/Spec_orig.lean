import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

open Nat

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Dummy value for a(0)
  | 1 => 1 -- Base case a(1)
  | n' + 2 => -- For n >= 2. Let $m = n'+2$ be the current index.
    -- The previous index is $j = n'+1 = m-1$.
    let j := n' + 1
    let a_j := a j
    -- The argument for gcd is $7j+6$.
    let k := 7 * j + 6
    let g := Nat.gcd a_j k
    -- Compute the absolute difference using integer casting and natAbs.
    Int.natAbs ((a_j : ℤ) - (g : ℤ))

lemma a_succ_succ (n : ℕ) : a (n + 2) = Int.natAbs ((a (n + 1) : ℤ) - (Nat.gcd (a (n + 1)) (7 * n + 13) : ℤ)) := by
  rfl

lemma a_2_eq_zero : a 2 = 0 := rfl

lemma a_23_eq_zero : a 23 = 0 := rfl

lemma prime_of_no_small_factors (M K : ℕ) (hM : M = 8 * K + 7) (hK : K ≥ 7) (hp : ∀ p, Nat.Prime p → p ∣ M → p > K) : Nat.Prime M := by
  by_contra h_not_prime
  have hM_pos : 0 < M := by
    rw [hM]
    omega
  have hM_ne_one : M ≠ 1 := by
    rw [hM]
    omega
  have hp_prime : Nat.Prime (minFac M) := minFac_prime hM_ne_one
  have hp_dvd : minFac M ∣ M := minFac_dvd M
  have hp_gt : minFac M > K := hp (minFac M) hp_prime hp_dvd
  have hp_ge : minFac M ≥ K + 1 := hp_gt
  have h_sq_le : (minFac M) ^ 2 ≤ M := minFac_sq_le_self hM_pos h_not_prime
  have h_sq_ge : (minFac M) ^ 2 ≥ (K + 1) ^ 2 := by
    nlinarith
  have h_contra : (K + 1) ^ 2 ≤ 8 * K + 7 := by
    linarith
  have h_algebra : K ^ 2 + 2 * K + 1 = (K + 1) ^ 2 := by
    ring
  have h_contra_expanded : K ^ 2 + 2 * K + 1 ≤ 8 * K + 7 := by
    rw [h_algebra]
    exact h_contra
  have h_contradiction : K < 7 := by
    nlinarith
  omega

def find_prev_zero (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | m + 2 => if a (m + 1) = 0 then m + 1 else find_prev_zero (m + 1)

lemma find_prev_zero_eq_zero (n : ℕ) : a (find_prev_zero n) = 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | m
  · rfl
  · rfl
  · dsimp [find_prev_zero]
    by_cases h : a (m + 1) = 0
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact ih (m + 1) (by omega)

lemma find_prev_zero_lt (n : ℕ) (hn : n > 2) : find_prev_zero n < n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | m
  · omega
  · omega
  · dsimp [find_prev_zero]
    by_cases h : a (m + 1) = 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      by_cases hm : m + 1 > 2
      · have h_lt := ih (m + 1) (by omega) hm
        omega
      · have hm1 : m = 1 := by omega
        rw [hm1] at h
        exact (h a_2_eq_zero).elim

lemma find_prev_zero_maximal (n : ℕ) (hn : n > 2) : ∀ m, find_prev_zero n < m → m < n → a m ≠ 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | m
  · omega
  · omega
  · intro k hk_gt hk_lt
    dsimp [find_prev_zero] at hk_gt
    by_cases h : a (m + 1) = 0
    · rw [if_pos h] at hk_gt
      omega
    · rw [if_neg h] at hk_gt
      by_cases h_k : k = m + 1
      · rw [h_k]
        exact h
      · have hk_lt' : k < m + 1 := by omega
        by_cases hm : m + 1 > 2
        · exact ih (m + 1) (by omega) hm k hk_gt hk_lt'
        · have hm1 : m = 1 := by omega
          rw [hm1] at h
          exact (h a_2_eq_zero).elim

lemma find_prev_zero_ge_2 (n : ℕ) (hn : n > 2) : find_prev_zero n ≥ 2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | m
  · omega
  · omega
  · dsimp [find_prev_zero]
    by_cases h : a (m + 1) = 0
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      by_cases hm : m + 1 > 2
      · exact ih (m + 1) (by omega) hm
      · have hm1 : m = 1 := by omega
        rw [hm1] at h
        exact (h a_2_eq_zero).elim

lemma a_succ_of_zero (s : ℕ) (h : a s = 0) (hs : s ≥ 2) : a (s + 1) = 7 * s + 6 := by
  rcases s with _ | _ | s'
  · omega
  · omega
  · have h1 : a (s' + 3) = Int.natAbs ((a (s' + 2) : ℤ) - (Nat.gcd (a (s' + 2)) (7 * (s' + 2) + 6) : ℤ)) := rfl
    rw [h] at h1
    simp only [Nat.gcd_zero_left] at h1
    have h2 : (((0:ℕ):ℤ) - ((7 * (s' + 2) + 6 : ℕ) : ℤ)).natAbs = 7 * (s' + 2) + 6 := by
      omega
    rw [h2] at h1
    exact h1

lemma prime_not_dvd_both (s p i : ℕ) (hs : s ≥ 2) (hp : Nat.Prime p) (hM : p ∣ 56 * s - 1) (hi : i < 7 * s - 1) :
  ¬ (p ∣ 7 * s - 1 - i ∧ p ∣ 7 * s + 7 * i + 13) := by
  intro ⟨h1, h2⟩
  have h3 : p ∣ 7 * (7 * s - 1 - i) + (7 * s + 7 * i + 13) := by
    exact dvd_add (dvd_mul_of_dvd_right h1 7) h2
  have h4 : 7 * (7 * s - 1 - i) + (7 * s + 7 * i + 13) = 56 * s + 6 := by
    omega
  rw [h4] at h3
  have h5 : p ∣ (56 * s + 6) - (56 * s - 1) := Nat.dvd_sub h3 hM
  have h6 : (56 * s + 6) - (56 * s - 1) = 7 := by omega
  rw [h6] at h5
  have h_prime_7 : Nat.Prime 7 := by decide
  have hp7 : p = 7 := by
    rcases h_prime_7.eq_one_or_self_of_dvd p h5 with h_one | h_self
    · rw [h_one] at hp
      exact (Nat.not_prime_one hp).elim
    · exact h_self
  rw [hp7] at hM
  have hM7 : 7 ∣ 56 * s - 1 := hM
  have hM7' : 7 ∣ 1 := by
    have h_sub : 7 ∣ 56 * s - (56 * s - 1) := Nat.dvd_sub ⟨8 * s, by ring⟩ hM7
    have h_sub_val : 56 * s - (56 * s - 1) = 1 := by omega
    rw [h_sub_val] at h_sub
    exact h_sub
  contradiction

lemma a_ne_zero_between_2_and_23 (n : ℕ) (h1 : 2 < n) (h2 : n < 23) : a n ≠ 0 := by
  interval_cases n <;> decide

lemma a_val_of_prime_helper (s n : ℕ) (hs : a s = 0) (hs2 : s ≥ 2) (hn : n > s) (h_no_zeros : ∀ m, s < m → m < n → a m ≠ 0) (h_prime : Nat.Prime (7 * s + 6)) :
  ∀ m, s < m → m ≤ n → a m = (7 * s + 6) - (m - (s + 1)) := by
  intro m hm_gt hm_le
  induction' m using Nat.strong_induction_on with m ih
  by_cases h_eq : m = s + 1
  · rw [h_eq]
    have h_sub_zero : s + 1 - (s + 1) = 0 := by omega
    rw [h_sub_zero]
    have h_sub_zero2 : 7 * s + 6 - 0 = 7 * s + 6 := by omega
    rw [h_sub_zero2]
    exact a_succ_of_zero s hs hs2
  · have hm_gt2 : m > s + 1 := by omega
    have hm_prev : m - 1 > s := by omega
    have hm_prev_le : m - 1 ≤ n := by omega
    have h_prev_eq := ih (m - 1) (by omega) hm_prev hm_prev_le
    have h_prev_ne_zero : a (m - 1) ≠ 0 := by
      by_cases h_eq_n : m - 1 = n
      · omega
      · have h_lt_n : m - 1 < n := by omega
        exact h_no_zeros (m - 1) hm_prev h_lt_n
    have h_gcd : Nat.gcd (a (m - 1)) (7 * (m - 1) + 6) = 1 := by
      by_contra h_gcd_ne_one
      have h_gcd_gt_one : Nat.gcd (a (m - 1)) (7 * (m - 1) + 6) > 1 := by
        have h_gcd_ne_zero : Nat.gcd (a (m - 1)) (7 * (m - 1) + 6) ≠ 0 := by
          have h_k_pos : 7 * (m - 1) + 6 ≠ 0 := by omega
          exact Nat.gcd_ne_zero_right h_k_pos
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h_gcd_ne_zero, h_gcd_ne_one⟩
      let p := minFac (Nat.gcd (a (m - 1)) (7 * (m - 1) + 6))
      have hp_prime : Nat.Prime p := minFac_prime (by omega)
      have hp_dvd_gcd : p ∣ Nat.gcd (a (m - 1)) (7 * (m - 1) + 6) := minFac_dvd _
      have hp_dvd_a : p ∣ a (m - 1) := hp_dvd_gcd.trans (Nat.gcd_dvd_left _ _)
      have hp_dvd_k : p ∣ 7 * (m - 1) + 6 := hp_dvd_gcd.trans (Nat.gcd_dvd_right _ _)
      let i := m - 1 - (s + 1)
      have hi_lt : i < 7 * s + 6 := by
        by_contra h_ge
        have h_eq_zero : a (m - 1) = 0 := by
          rw [h_prev_eq]
          omega
        exact h_prev_ne_zero h_eq_zero
      have hp_dvd_sum : p ∣ 56 * (s + 1) - 1 := by
        have h_m_eq : m - 1 = s + 1 + i := by omega
        have h_sum : 56 * (s + 1) - 1 = 7 * (7 * s + 6 - i) + (7 * (m - 1) + 6) := by
          omega
        rw [h_sum]
        have hp_dvd_left : p ∣ 7 * (7 * s + 6 - i) := dvd_mul_of_dvd_right (by rw [← h_prev_eq]; exact hp_dvd_a) 7
        exact dvd_add hp_dvd_left hp_dvd_k
      have h_not_dvd := prime_not_dvd_both (s + 1) p i (by omega) hp_prime hp_dvd_sum hi_lt
      have hp_dvd_both : p ∣ 7 * (s + 1) - 1 - i ∧ p ∣ 7 * (s + 1) + 7 * i + 13 := by
        sorry
      exact h_not_dvd hp_dvd_both
    -- Now we show a m = a (m - 1) - 1
    have h_rec : a m = a (m - 1) - 1 := by
      have h_rec_orig : a m = Int.natAbs ((a (m - 1) : ℤ) - (Nat.gcd (a (m - 1)) (7 * (m - 1) + 6) : ℤ)) := by
        rcases m with _ | _ | m'
        · omega
        · omega
        · rfl
      rw [h_gcd] at h_rec_orig
      have h_abs : Int.natAbs ((a (m - 1) : ℤ) - ((1:ℕ):ℤ)) = a (m - 1) - 1 := by
        have h_pos : a (m - 1) ≥ 1 := by
          exact Nat.pos_of_ne_zero h_prev_ne_zero
        omega
      exact h_rec_orig.trans h_abs
    rw [h_rec]
    rw [h_prev_eq]
    omega

theorem oeis_261307_conjecture_0 : ∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro hn han
  let s := find_prev_zero n
  have hs_lt := find_prev_zero_lt n hn
  have hs_eq := find_prev_zero_eq_zero n
  have hs_ge2 := find_prev_zero_ge_2 n hn
  have h_maximal := find_prev_zero_maximal n hn
  by_cases hs2 : s = 2
  · have hn23 : n = 23 := by
      by_contra h_ne
      have h_cases : n < 23 ∨ n > 23 := by omega
      rcases h_cases with h_lt | h_gt
      · have h_ne_zero := a_ne_zero_between_2_and_23 n hn h_lt
        exact h_ne_zero han
      · have h23_ne_zero : a 23 ≠ 0 := by
          have hs2_eq : find_prev_zero n = 2 := hs2
          rw [hs2_eq] at h_maximal
          exact h_maximal 23 (by omega) h_gt
        exact h23_ne_zero a_23_eq_zero
    rw [hn23]
    decide
  · have hs_gt2 : s > 2 := by
      have hs_neq : find_prev_zero n ≠ 2 := hs2
      omega
    have hp_s : Nat.Prime (7 * s + 6) := ih s hs_lt hs_gt2 hs_eq
    let K := 7 * s + 6
    have h_helper := a_val_of_prime_helper s n hs_eq hs_ge2 hs_lt h_maximal hp_s
    have hn_le : n ≤ s + K + 1 := by
      by_contra h_gt
      have h_m : s + K + 1 < n := by omega
      have h_val_m := h_helper (s + K + 1) (by omega) (by omega)
      have h_m_sub : s + K + 1 - (s + 1) = K := by omega
      rw [h_m_sub] at h_val_m
      have h_K_sub : K - K = 0 := by omega
      rw [h_K_sub] at h_val_m
      have h_ne_zero := h_maximal (s + K + 1) (by omega) h_m
      exact h_ne_zero h_val_m
    have hn_ge : n ≥ s + K + 1 := by
      have h_val := h_helper n hs_lt (by omega)
      rw [han] at h_val
      omega
    have h_n_eq : n = s + K + 1 := by omega
    have h_7n_eq : 7 * n + 6 = 8 * K + 7 := by
      rw [h_n_eq]
      omega
    rw [h_7n_eq]
    apply prime_of_no_small_factors (8 * K + 7) K rfl (by omega)
    intro p hp_prime hp_dvd
    by_contra h_le_K
    have h_le_K_nat : p ≤ K := by omega
    by_cases hp_eq_K : p = K
    · rw [hp_eq_K] at hp_dvd
      have h_dvd_7 : K ∣ 7 := by
        have h_mult : K ∣ 8 * K := dvd_mul_left K 8
        exact (Nat.dvd_add_right h_mult).mp hp_dvd
      have h_le_7 : K ≤ 7 := Nat.le_of_dvd (by decide) h_dvd_7
      omega
    · have hp_lt_K : p < K := by omega
      let i := K - p
      have hp_ge2 : p ≥ 2 := Nat.Prime.two_le hp_prime
      have hi_lt : i < 7 * s + 6 := by omega
      have hp_dvd_both : p ∣ 7 * (s + 1) - 1 - i ∧ p ∣ 7 * (s + 1) + 7 * i + 13 := by
        sorry
      have hp_dvd_sum : p ∣ 56 * (s + 1) - 1 := by
        have h_sum_val : 56 * (s + 1) - 1 = 8 * K + 7 := by omega
        rw [h_sum_val]
        exact hp_dvd
      have h_not_dvd := prime_not_dvd_both (s + 1) p i (by omega) hp_prime hp_dvd_sum hi_lt
      exact h_not_dvd hp_dvd_both
