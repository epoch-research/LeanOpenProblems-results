# -*- coding: utf-8 -*-
import os

with open('/workspace/leanproject/Submission/Spec.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# 1. Define our correct helper theorems
helpers = """theorem prime_divisors_sum {p : ℕ} (hp : Nat.Prime p) : p.divisors.sum id = p + 1 := by
  rw [Nat.Prime.divisors hp]
  have : 1 ≠ p := hp.ne_one.symm
  rw [sum_insert (by simp [this]), sum_singleton, id_eq, id_eq]
  omega

theorem hd_odd_test (d k : ℕ) (h : (d * k) % 2 = 1) : d % 2 = 1 := by
  have h_mul : (d * k) % 2 = (d % 2 * (k % 2)) % 2 := Nat.mul_mod d k 2
  rw [h_mul] at h
  rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · rw [hd0] at h
    simp only [zero_mul, zero_mod, zero_ne_one] at h
  · exact hd1

theorem divisors_prime_sq {d : ℕ} (hd : Nat.Prime d) : (d * d).divisors = {1, d, d * d} := by
  ext x
  rw [mem_divisors]
  have hd2 : d * d = d ^ 2 := by ring
  have h_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd.ne_zero
  rw [hd2]
  simp only [and_iff_left h_ne]
  rw [Nat.dvd_prime_pow hd]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; exact pow_zero d
    · right; left; exact pow_one d
    · right; right; ring
  · rintro (rfl | rfl | rfl)
    · refine ⟨0, by decide, (pow_zero d).symm⟩
    · refine ⟨1, by decide, (pow_one d).symm⟩
    · refine ⟨2, by decide, by ring⟩

theorem sum_divisors_prime_sq {d : ℕ} (hd : Nat.Prime d) : (d * d).divisors.sum id = 1 + d + d * d := by
  rw [divisors_prime_sq hd]
  have h1d : 1 ≠ d := hd.ne_one.symm
  have hdm : d ≠ d * d := by
    intro hc
    have h_eq : d * 1 = d * d := by
      rw [mul_one]
      exact hc
    have : 1 = d := Nat.eq_of_mul_eq_mul_left hd.pos h_eq
    omega
  have h1m : 1 ≠ d * d := by
    intro hc
    have : d * d ≥ 2 * 2 := Nat.mul_le_mul hd.two_le hd.two_le
    omega
  rw [sum_insert (by simp [h1d, h1m]), sum_insert (by simp [hdm]), sum_singleton, id_eq, id_eq, id_eq]
  ring

theorem test_minfac (m : ℕ) (hm : m ≥ 3) (hm_odd : m % 2 = 1) :
    Nat.Prime (minFac m) ∧ minFac m ∣ m ∧ minFac m ≥ 3 := by
  have h1 : minFac m ∣ m := minFac_dvd m
  have h_ne : m ≠ 1 := by omega
  have h2 : Nat.Prime (minFac m) := minFac_prime h_ne
  have h3 : minFac m ≥ 3 := by
    have : minFac m ≠ 2 := by
      intro hc
      have : 2 ∣ m := by
        rw [← hc]
        exact h1
      have : m % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      omega
    have : minFac m ≠ 1 := h2.ne_one
    have : minFac m ≠ 0 := h2.ne_zero
    omega
  exact ⟨h2, h1, h3⟩

theorem test_div (m a s_sum : ℕ) (ha : a ≥ 1) (hm : m ≥ 3)
    (h_eq : (2^(a+1) - 1) * s_sum = 2^(a+1) * m - 1) : (2^(a+1) - 1) ∣ (m - 1) := by
  have h_pow_ge : 2^(a+1) ≥ 4 := by
    have h_exp : a + 1 ≥ 2 := by omega
    have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
    exact h_two
  have h_pow_pos : 2^(a+1) * m ≥ m := by
    have : 2^(a+1) ≥ 1 := by omega
    exact Nat.le_mul_of_pos_left m (by omega)
  have h_eq2 : 2^(a+1) * m - 1 = (2^(a+1) - 1) * m + (m - 1) := by
    rw [Nat.sub_mul, one_mul]
    omega
  have h_div : (2^(a+1) - 1) ∣ (2^(a+1) - 1) * m + (m - 1) := by
    use s_sum
    rw [h_eq]
    exact h_eq2.symm
  have h_self : (2^(a+1) - 1) ∣ (2^(a+1) - 1) * m := dvd_mul_right (2^(a+1) - 1) m
  exact (Nat.dvd_add_iff_right h_self).mpr h_div

theorem test_c_even (m a c : ℕ) (hm_odd : m % 2 = 1) (hm : m ≥ 3) (ha : a ≥ 1)
    (hc : m - 1 = (2^(a+1) - 1) * c) : c % 2 = 0 := by
  by_contra hc_odd
  have hc_odd' : c % 2 = 1 := by omega
  have h_pow_even : 2^(a+1) % 2 = 0 := by
    rw [pow_succ]
    rw [Nat.mul_mod]
    simp
  have h_pow_ge : 2^(a+1) ≥ 2 := by
    have h_exp : a + 1 ≥ 2 := by omega
    have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
    omega
  have h_pow_odd : (2^(a+1) - 1) % 2 = 1 := by
    omega
  have h_prod : ((2^(a+1) - 1) * c) % 2 = 1 := by
    rw [Nat.mul_mod, h_pow_odd, hc_odd']
  have h_even : (m - 1) % 2 = 0 := by omega
  omega

theorem test_formula_derivation (Y k s_sum : ℕ) (h_pow_ge : Y ≥ 4)
    (h_eq : Y * ((Y - 1) * (2 * k) + 1) = (Y - 1) * s_sum + 1) :
    s_sum = 2 * k * Y + 1 := by
  have h_rw : Y * ((Y - 1) * (2 * k) + 1) = (Y - 1) * (2 * k * Y) + Y := by
    have h_mul : Y * ((Y - 1) * (2 * k) + 1) = Y * ((Y - 1) * (2 * k)) + Y := by ring
    rw [h_mul]
    congr 1
    ring
  rw [h_rw] at h_eq
  have h_eq2 : (Y - 1) * (2 * k * Y) + Y = (Y - 1) * (2 * k * Y + 1) + 1 := by
    rw [mul_add, mul_one]
    omega
  rw [h_eq2] at h_eq
  have h_eq3 : (Y - 1) * (2 * k * Y + 1) = (Y - 1) * s_sum := by omega
  have h_Y_sub_ne : Y - 1 ≠ 0 := by omega
  exact (Nat.mul_right_inj h_Y_sub_ne).mp h_eq3.symm

theorem test_sum_mk (Y k m s_sum : ℕ) (h_pow_ge : Y ≥ 4)
    (h_deriv : s_sum = 2 * k * Y + 1)
    (h_m_eq : m = (Y - 1) * (2 * k) + 1) : s_sum = m + 2 * k := by
  rw [h_deriv, h_m_eq]
  have h_sub : (Y - 1) * (2 * k) = Y * (2 * k) - 2 * k := by
    rw [Nat.sub_mul, one_mul]
  rw [h_sub]
  have : Y * (2 * k) ≥ 2 * k := by
    have : Y ≥ 1 := by omega
    exact Nat.le_mul_of_pos_left (2 * k) (by omega)
  have h_ring : 2 * k * Y = Y * (2 * k) := by ring
  rw [h_ring]
  omega

theorem test_prime_D_one (m a : ℕ) (hm_odd : m % 2 = 1) (hp : Nat.Prime m) (h_sum : m.divisors.sum id = m + 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  rw [h_sum] at h_D
  have h_eq : 2^(a+1) * m = (2^(a+1) - 1) * (m + 1) + 1 := by omega
  have h_ring : (2^(a+1) - 1) * (m + 1) + 1 = 2^(a+1) * m + 2^(a+1) - m := by
    have h_pow_pos : 2^(a+1) ≥ 1 := by omega
    have h_mul : (2^(a+1) - 1) * (m + 1) = 2^(a+1) * (m + 1) - (m + 1) := by
      rw [Nat.sub_mul, one_mul]
    rw [h_mul]
    have h_pos : 2^(a+1) * (m + 1) ≥ m + 1 := Nat.le_mul_of_pos_left (m + 1) h_pow_pos
    omega
  rw [h_ring] at h_eq
  have hp_eq : m = 2^(a+1) := by omega
  have hp_even : m % 2 = 0 := by
    rw [hp_eq]
    rw [pow_succ]
    simp
  omega

theorem h_sum_ne2 {m : ℕ} (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) : m.divisors.sum id ≠ 2 * m - 1 := by
  intro h_sum
  by_cases hp : Nat.Prime m
  · have : m.divisors.sum id = m + 1 := prime_divisors_sum hp
    omega
  · have hm_ge2 : 2 ≤ m := by omega
    let d := minFac m
    have hd_prime : Nat.Prime d := Nat.minFac_prime (by omega)
    have hd : d ∣ m := minFac_dvd m
    have hd_ge2 : 2 ≤ d := hd_prime.two_le
    have hd_le : d ≤ m := Nat.le_of_dvd (by omega) hd
    have hd_ne : d ≠ m := by
      intro hc
      have : Nat.Prime m := by rwa [← hc]
      exact hp this
    have hd_lt : d < m := lt_of_le_of_ne hd_le hd_ne
    have hd_odd : d % 2 = 1 := hd_odd_test d (m/d) (by rwa [Nat.mul_div_cancel' hd] at hm_odd)
    have hd_ge3 : d ≥ 3 := by omega
    have hd_div : m/d ∣ m := Nat.div_dvd_of_dvd hd
    have hd_div_ge3 : m/d ≥ 3 := by
      generalize hk : m / d = k
      have : k ≠ 1 := by
        intro hc
        have : m = d := by
          rw [← Nat.div_mul_cancel hd, hk, hc, one_mul]
        omega
      have : k ≠ 0 := by
        intro hc
        have : m = 0 := by
          rw [← Nat.div_mul_cancel hd, hk, hc, zero_mul]
        omega
      have h_odd2 : k % 2 = 1 := by
        rw [← hk]
        exact hd_odd_test (m/d) d (by rwa [Nat.mul_comm, Nat.div_mul_cancel hd] at hm_odd)
      have : k ≠ 2 := by
        intro hc
        rw [hc] at h_odd2
        contradiction
      omega
    by_cases hd_eq : d = m/d
    · have : m = d * d := by
        have h_eq : m = (m / d) * d := (Nat.div_mul_cancel hd).symm
        rw [← hd_eq] at h_eq
        exact h_eq
      have h_sum_sq : m.divisors.sum id = 1 + d + d * d := by
        rw [this]
        exact sum_divisors_prime_sq hd_prime
      have h_sum' : 1 + d + d * d = 2 * (d * d) - 1 := by
        rwa [h_sum_sq, this] at h_sum
      have h_ring_contra : (d - 1) * (d - 2) = 0 := by
        omega
      omega
    · have h1 : 1 ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨one_dvd m, by omega⟩
      have h_d : d ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨hd, by omega⟩
      have h_md : m/d ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨hd_div, by omega⟩
      have hm : m ∈ m.divisors := by
        rw [mem_divisors]
        exact ⟨dvd_rfl, by omega⟩
      have h1d : 1 ≠ d := by omega
      have h1md : 1 ≠ m/d := by omega
      have h1m : 1 ≠ m := by omega
      have hdm : d ≠ m := by omega
      have hmdm : m/d ≠ m := by
        intro hc
        have : m = (m/d) * d := (Nat.div_mul_cancel hd).symm
        rw [hc] at this
        have : d = 1 := by
          have h_m_pos : m > 0 := by omega
          exact Nat.eq_of_mul_eq_mul_right (by omega) this
        omega
      have h_sub : {1, d, m/d, m} ⊆ m.divisors := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h1
        · exact h_d
        · exact h_md
        · exact hm
      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
        have h_sum_four : ({1, d, m/d, m} : Finset ℕ).sum id = 1 + d + m/d + m := by
          rw [sum_insert (by simp [h1d, h1md, h1m]), sum_insert (by simp [hd_eq, hdm]), sum_insert (by simp [hmdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
          omega
        rw [← h_sum_four]
        exact sum_le_sum_of_subset h_sub
      omega

theorem D_ne_one (m a : ℕ) (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) (hp : ¬Nat.Prime m)
    (h_sum_ne2 : m.divisors.sum id ≠ 2 * m - 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add, pow_one] at h_D
    have : m.divisors.sum id = 2 * m - 1 := by omega
    exact h_sum_ne2 this
  · have ha : a ≥ 1 := by omega
    have h_pow_ge : 2^(a+1) ≥ 4 := by
      have h_exp : a + 1 ≥ 2 := by omega
      have h_two : 2^2 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) h_exp
      exact h_two
    have h_eq : (2^(a+1) - 1) * m.divisors.sum id = 2^(a+1) * m - 1 := by omega
    have h_div := test_div m a (m.divisors.sum id) ha hm_ge h_eq
    rcases h_div with ⟨c, hc⟩
    have hc_even : c % 2 = 0 := test_c_even m a c hm_odd hm_ge ha hc
    have h_dvd_c : 2 ∣ c := dvd_of_mod_eq_zero hc_even
    rcases h_dvd_c with ⟨k, rfl⟩
    have h_eq_add : 2^(a+1) * m = (2^(a+1) - 1) * m.divisors.sum id + 1 := by omega
    have h_m_eq : m = (2^(a+1) - 1) * (2 * k) + 1 := by omega
    have h_eq_add' : 2^(a+1) * ((2^(a+1) - 1) * (2 * k) + 1) = (2^(a+1) - 1) * m.divisors.sum id + 1 := by
      calc 2^(a+1) * ((2^(a+1) - 1) * (2 * k) + 1)
        _ = 2^(a+1) * m := by rw [h_m_eq]
        _ = (2^(a+1) - 1) * m.divisors.sum id + 1 := h_eq_add
    have h_deriv := test_formula_derivation (2^(a+1)) k (m.divisors.sum id) h_pow_ge h_eq_add'
    rcases test_minfac m hm_ge hm_odd with ⟨hp_p, hd_p, hp_ge3⟩
    have h_prime_p : Nat.Prime (minFac m) := hp_p
    have hd_p : minFac m ∣ m := hd_p
    have hp_ge3 : minFac m ≥ 3 := hp_ge3
    let p := minFac m
    have h_pd : p * (m / p) = m := Nat.mul_div_cancel' hd_p
    generalize hd_eq : m / p = d
    rw [hd_eq] at h_pd
    have hd_dvd : d ∣ m := by
      use p
      rw [mul_comm]
      exact h_pd.symm
    have hp_ne_m : p ≠ m := by
      intro hc_pm
      have : minFac m = m := hc_pm
      rw [this] at h_prime_p
      exact hp h_prime_p
    have hd_gt1 : d ≥ 2 := by
      have hd1' : d ≠ 1 := by
        intro hc
        have h_pm : p = m := by
          rw [hc, mul_one] at h_pd
          exact h_pd
        exact hp_ne_m h_pm
      have hd0 : d ≠ 0 := by
        intro hc
        have h_zero : p * 0 = 0 := mul_zero p
        have : 0 = m := by
          rw [← h_zero]
          rw [← hc]
          exact h_pd
        omega
      omega
    have hd_lt_m : d < m := by
      have : 3 * d ≤ p * d := Nat.mul_le_mul_right d hp_ge3
      rw [h_pd] at this
      omega
    have hp_odd : p % 2 = 1 := hd_odd_test p d (by rwa [h_pd] at hm_odd)
    have h_sum_mk := test_sum_mk (2^(a+1)) k m (m.divisors.sum id) h_pow_ge h_deriv h_m_eq
    have hp_ne_d : p ≠ d := by
      intro hc
      have h_sum_sq : m.divisors.sum id = 1 + p + p * p := by
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq]
        exact sum_divisors_prime_sq h_prime_p
      have h_2k : 2 * k = p + 1 := by
        have h_sum_mk' := h_sum_mk
        rw [h_sum_sq] at h_sum_mk'
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq] at h_sum_mk'
        omega
      have h_alg : p * p = (2^(a+1) - 1) * (p + 1) + 1 := by
        have h_m_eq' := h_m_eq
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq] at h_m_eq'
        rw [h_2k] at h_m_eq'
        exact h_m_eq'
      have h_alg2 : p * (p + 1) = 2^(a+1) * (p + 1) := by
        have h_sub_mul : (2^(a+1) - 1) * (p + 1) = 2^(a+1) * (p + 1) - (p + 1) := by
          rw [Nat.sub_mul, one_mul]
        rw [h_sub_mul] at h_alg
        have h_pos : 2^(a+1) * (p + 1) > 0 := by positivity
        omega
      have hp_eq : p = 2^(a+1) := Nat.eq_of_mul_eq_mul_right (by omega) h_alg2
      have hp_even : p % 2 = 0 := by
        rw [hp_eq]
        rw [pow_succ]
        simp
      omega
    have hd_odd : d % 2 = 1 := hd_odd_test d p (by rwa [mul_comm, h_pd] at hm_odd)
    have hd1 : 1 ∈ m.divisors := by rw [mem_divisors]; exact ⟨one_dvd m, by omega⟩
    have h_p : p ∈ m.divisors := by rw [mem_divisors]; exact ⟨hd_p, by omega⟩
    have h_d : d ∈ m.divisors := by rw [mem_divisors]; exact ⟨hd_dvd, by omega⟩
    have hm : m ∈ m.divisors := by rw [mem_divisors]; exact ⟨dvd_rfl, by omega⟩
    have h1p : 1 ≠ p := by omega
    have h1d : 1 ≠ d := by omega
    have hpd : p ≠ d := hp_ne_d
    have hpm : p ≠ m := hp_ne_m
    have hdm : d ≠ m := by omega
    have h1m : 1 ≠ m := by omega
    have h_sub : {1, p, d, m} ⊆ m.divisors := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hd1
      · exact h_p
      · exact h_d
      · exact hm
    have h_sum_ge : 1 + p + d + m ≤ m.divisors.sum id := by
      have h_sum_four : ({1, p, d, m} : Finset ℕ).sum id = 1 + p + d + m := by
        rw [sum_insert (by simp [h1p, h1d, h1m]), sum_insert (by simp [hpd, hpm]), sum_insert (by simp [hdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
        omega
      rw [← h_sum_four]
      exact sum_le_sum_of_subset h_sub
    have h_3d_le : 3 * d ≤ m := by
      have : 3 * d ≤ p * d := Nat.mul_le_mul_right d hp_ge3
      rw [h_pd] at this
      exact this
    have h_bound1 : m ≥ 6 * k + 1 := by
      have : 2^(a+1) - 1 ≥ 3 := by omega
      nlinarith
    have h_2k_ge : 2 * k ≥ p + d + 2 := by
      have h_ge : 2 * k ≥ p + d + 1 := by omega
      have h_ne : 2 * k ≠ p + d + 1 := by
        intro hc
        have h_even : (2 * k) % 2 = 0 := by simp
        have h_odd : (p + d + 1) % 2 = 1 := by omega
        omega
      omega
    by_cases hp3 : p = 3
    · subst hp3
      omega
    · have hp_ge5 : p ≥ 5 := by omega
      have hd_ge5 : d ≥ 5 := by
        by_cases hd_pr : Nat.Prime d
        · have : d > p := by
            have : d ≥ p := by
              have hd_dvd' : d ∣ m := hd_dvd
              have : minFac m ≤ d := Nat.minFac_le_of_dvd (by omega) hd_dvd'
              exact this
            omega
          omega
        · have hd_ge2 : d ≥ 2 := by omega
          let q := minFac d
          have hq_pr : Nat.Prime q := Nat.minFac_prime (by omega)
          have hq_dvd : q ∣ d := minFac_dvd d
          have hq_dvd_m : q ∣ m := dvd_trans hq_dvd hd_dvd
          have hp_le_q : p ≤ q := Nat.minFac_le_of_dvd (by omega) hq_dvd_m
          have hd_div_q_ge3 : d / q ≥ 3 := by
            have : d / q ≠ 1 := by
              intro hc
              have : d = q := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, one_mul]
              have : Nat.Prime d := by rwa [← this]
              contradiction
            have : d / q ≠ 0 := by
              intro hc
              have : d = 0 := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, zero_mul]
              omega
            have h_odd_div : (d / q) % 2 = 1 := hd_odd_test (d / q) q (by rwa [Nat.div_mul_cancel hq_dvd])
            have : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            omega
          have : d = q * (d / q) := (Nat.div_mul_cancel hq_dvd).symm
          nlinarith
      omega
"""

# Replace in content
start_idx = content.find("theorem h_sum_ne2 {m : ℕ} (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) : m.divisors.sum id ≠ 2 * m - 1 := by")
end_idx = content.find("theorem S_le_two_pow")

if start_idx == -1 or end_idx == -1:
    print("Error: Could not find markers for h_sum_ne2 replacement!")
    exit(1)

content_patched = content[:start_idx] + helpers + content[end_idx:]

# Replace the D = 1 case of S_le_two_pow
start_d1_idx = content_patched.find("· have h_D_one : D = 1 := by omega")
end_d1_idx = content_patched.find("· clear D h_D_ge_one h_D")

if start_d1_idx == -1 or end_d1_idx == -1:
    # Try with raw middle dot instead
    start_d1_idx = content_patched.find("      \u00b7 have h_D_one : D = 1 := by omega")
    # find next line containing "clear D"
    end_d1_idx = content_patched.find("    \u00b7 clear D h_D_ge_one h_D")

if start_d1_idx == -1 or end_d1_idx == -1:
    print("Error: Could not find markers for D = 1 replacement!")
    # Let's inspect what is in content_patched
    print("start_d1_idx:", start_d1_idx, "end_d1_idx:", end_d1_idx)
    exit(1)

replacement_d1 = """      · have h_D_one : D = 1 := by omega
        by_cases hp : Nat.Prime m
        · have h_sum_pr : m.divisors.sum id = m + 1 := prime_divisors_sum hp
          have h_false : False := test_prime_D_one m a hm_odd hp h_sum_pr h_D_one
          exact False.elim h_false
        · have h_sum_ne2' : m.divisors.sum id ≠ 2 * m - 1 := h_sum_ne2 hm_odd hm_ge_three
          have h_false : False := D_ne_one m a hm_odd hm_ge_three hp h_sum_ne2' h_D_one
          exact False.elim h_false
    """

content_final = content_patched[:start_d1_idx] + replacement_d1 + content_patched[end_d1_idx:]

# Write back
with open('/workspace/leanproject/Submission/Spec.lean', 'w', encoding='utf-8') as f:
    f.write(content_final)

print("Spec.lean successfully patched and written!")
