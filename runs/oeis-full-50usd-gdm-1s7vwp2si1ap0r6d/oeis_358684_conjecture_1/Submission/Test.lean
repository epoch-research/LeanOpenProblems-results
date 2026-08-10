import FormalConjectures.Util.ProblemImports

open Nat

set_option exponentiation.threshold 20000000
set_option maxRecDepth 20000

def check_no_factor_range (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) : Bool :=
  match k with
  | 0 => true
  | k' + 1 =>
    let p := (start + k') * modulus_shift + 1
    if F % p == 0 then
      false
    else
      check_no_factor_range F modulus_shift start k'

theorem check_no_factor_range_correct (F : ℕ) (modulus_shift : ℕ) (start : ℕ) (k : ℕ) (q_k : ℕ) (q : ℕ)
    (hq : q = q_k * modulus_shift + 1) (hq_ge : start ≤ q_k) (hq_lt : q_k < start + k) (hq_pos : 0 < q_k)
    (h_check : check_no_factor_range F modulus_shift start k = true) :
    ¬ (q ∣ F) := by
  induction k generalizing q_k q with
  | zero =>
    omega
  | succ k' ih =>
    unfold check_no_factor_range at h_check
    simp only at h_check
    by_cases h_dvd : (F % ((start + k') * modulus_shift + 1) == 0) = true
    · rw [h_dvd] at h_check
      contradiction
    · have h_false : (F % ((start + k') * modulus_shift + 1) == 0) = false := by
        cases h_c : F % ((start + k') * modulus_shift + 1) == 0
        · rfl
        · contradiction
      rw [h_false] at h_check
      have h_not_dvd : ¬ ((start + k') * modulus_shift + 1 ∣ F) := by
        intro hd
        rw [Nat.dvd_iff_mod_eq_zero] at hd
        have h_true : (F % ((start + k') * modulus_shift + 1) == 0) = true := by
          rw [beq_iff_eq]
          exact hd
        rw [h_true] at h_false
        contradiction
      have h_cases : q_k = start + k' ∨ q_k < start + k' := by omega
      rcases h_cases with rfl | h_lt
      · subst hq
        exact h_not_dvd
      · exact ih q_k q hq hq_ge h_lt hq_pos h_check

theorem prime_31065037602817 : Nat.Prime 31065037602817 := by norm_num

theorem check_f17_0 : check_no_factor_range (fermatNumber 17) (2^19) 1 4999 = true := by
  decide

theorem check_f17_1 : check_no_factor_range (fermatNumber 17) (2^19) 5000 5000 = true := by
  decide

theorem check_f17_2 : check_no_factor_range (fermatNumber 17) (2^19) 10000 5000 = true := by
  decide

theorem check_f17_3 : check_no_factor_range (fermatNumber 17) (2^19) 15000 5000 = true := by
  decide

theorem check_f17_4 : check_no_factor_range (fermatNumber 17) (2^19) 20000 5000 = true := by
  decide

theorem check_f17_5 : check_no_factor_range (fermatNumber 17) (2^19) 25000 5000 = true := by
  decide

theorem check_f17_6 : check_no_factor_range (fermatNumber 17) (2^19) 30000 5000 = true := by
  decide

theorem check_f17_7 : check_no_factor_range (fermatNumber 17) (2^19) 35000 5000 = true := by
  decide

theorem check_f17_8 : check_no_factor_range (fermatNumber 17) (2^19) 40000 5000 = true := by
  decide

theorem check_f17_9 : check_no_factor_range (fermatNumber 17) (2^19) 45000 5000 = true := by
  decide

theorem check_f17_10 : check_no_factor_range (fermatNumber 17) (2^19) 50000 5000 = true := by
  decide

theorem check_f17_11 : check_no_factor_range (fermatNumber 17) (2^19) 55000 4251 = true := by
  decide

theorem minFac_F_17 : minFac (fermatNumber 17) = 31065037602817 := by
  have h_dvd : 31065037602817 ∣ fermatNumber 17 := by
    rw [← ZMod.natCast_eq_zero_iff]
    unfold fermatNumber; push_cast; reduce_mod_char
  have h1 : minFac (fermatNumber 17) ≤ 31065037602817 := by
    apply minFac_le_of_dvd
    · decide
    · exact h_dvd
  have h2 : 31065037602817 ≤ minFac (fermatNumber 17) := by
    have h2' : ∀ q, Prime q → q ∣ fermatNumber 17 → 31065037602817 ≤ q := by
      intro q hq_prime hq_dvd
      obtain ⟨k, hq_eq⟩ := fermat_primeFactors_one_lt 17 q (by decide) hq_prime hq_dvd
      have hk_pos : 0 < k := by
        by_contra hk_zero
        have hk0 : k = 0 := by omega
        subst hk0
        rw [zero_mul, zero_add] at hq_eq
        subst hq_eq
        exact hq_prime.ne_one rfl
      have h_cases : k ≥ 59251 ∨ k < 59251 := by omega
      rcases h_cases with hk_ge | hk_lt
      · rw [hq_eq]
        have : 31065037602817 = 59251 * 2^19 + 1 := by rfl
        rw [this]
        gcongr
      have h_cases_split : k < 5000 ∨ (5000 ≤ k ∧ k < 10000) ∨ (10000 ≤ k ∧ k < 15000) ∨ (15000 ≤ k ∧ k < 20000) ∨ (20000 ≤ k ∧ k < 25000) ∨ (25000 ≤ k ∧ k < 30000) ∨ (30000 ≤ k ∧ k < 35000) ∨ (35000 ≤ k ∧ k < 40000) ∨ (40000 ≤ k ∧ k < 45000) ∨ (45000 ≤ k ∧ k < 50000) ∨ (50000 ≤ k ∧ k < 55000) ∨ (55000 ≤ k ∧ k < 59251) := by omega
      rcases h_cases_split with h_range | h_range | h_range | h_range | h_range | h_range | h_range | h_range | h_range | h_range | h_range | h_range
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 1 4999 k q hq_eq hk_pos h_range hk_pos check_f17_0
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 5000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_1
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 10000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_2
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 15000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_3
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 20000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_4
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 25000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_5
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 30000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_6
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 35000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_7
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 40000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_8
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 45000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_9
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 50000 5000 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_10
        exact h_not_dvd hq_dvd
      · have h_not_dvd := check_no_factor_range_correct (fermatNumber 17) (2^19) 55000 4251 k q hq_eq h_range.1 h_range.2 hk_pos check_f17_11
        exact h_not_dvd hq_dvd
    have h2_or := le_minFac.mpr h2'
    rcases h2_or with h_one | h_le
    · exfalso
      have : 3 ≤ fermatNumber 17 := three_le_fermatNumber 17
      rw [h_one] at this
      omega
    · exact h_le
  exact le_antisymm h1 h2