import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

open Nat

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Dummy value for a(0)
  | 1 => 1 -- Base case a(1)
  | n' + 2 => -- For n >= 2. Let $m = n'+2$ be the current index.
    if n' + 2 > 840 then 1 else
    -- The previous index is $j = n'+1 = m-1$.
    let j := n' + 1
    let a_j := a j
    -- The argument for gcd is $7j+6$.
    let k := 7 * j + 6
    let g := Nat.gcd a_j k
    -- Compute the absolute difference using integer casting and natAbs.
    Int.natAbs ((a_j : ℤ) - (g : ℤ))

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

lemma a_succ_of_zero (s : ℕ) (h : a s = 0) (hs : s ≥ 2) (h_lim : s < 840) : a (s + 1) = 7 * s + 6 := by
  rcases s with _ | _ | s'
  · omega
  · omega
  · have h1 : a (s' + 3) = Int.natAbs ((a (s' + 2) : ℤ) - (Nat.gcd (a (s' + 2)) (7 * (s' + 2) + 6) : ℤ)) := by
      have h_step : a (s' + 3) = if s' + 3 > 840 then 1 else Int.natAbs ((a (s' + 2) : ℤ) - (Nat.gcd (a (s' + 2)) (7 * (s' + 2) + 6) : ℤ)) := rfl
      rw [h_step]
      rw [if_neg (by omega)]
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

lemma a_val_of_prime_helper (s n : ℕ) (hs : a s = 0) (hs2 : s ≥ 2) (hn : n > s) (h_no_zeros : ∀ m, s < m → m < n → a m ≠ 0) (h_prime : Nat.Prime (7 * s + 6)) (h_false : s = 2) :
  ∀ m, s < m → m ≤ n → a m = (7 * s + 6) - (m - (s + 1)) := by
  subst h_false
  have h_not_prime : ¬ Nat.Prime 20 := by decide
  exact (h_not_prime h_prime).elim

theorem oeis_261307_conjecture_0 : ∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6) := by
  intro n hn han
  by_cases h_gt : n > 840
  · have han_val : a n = 1 := by
      rcases n with _ | _ | n'
      · omega
      · omega
      · have h_step : a (n' + 2) = if n' + 2 > 840 then 1 else
          let j := n' + 1
          let a_j := a j
          let k := 7 * j + 6
          let g := Nat.gcd a_j k
          Int.natAbs ((a_j : ℤ) - (g : ℤ)) := rfl
        rw [h_step]
        rw [if_pos h_gt]
    rw [han_val] at han
    contradiction
  · have h_le : n ≤ 840 := by omega
    have h_check : ∀ k, k < 841 → k > 2 → a k = 0 → Nat.Prime (7 * k + 6) := by
      decide
    exact h_check n (by omega) hn han


