import Mathlib

open Nat

lemma odd_of_not_two_dvd {m : ℕ} (h : ¬ 2 ∣ m) : Odd m := by
  have h1 : m % 2 ≠ 0 := by
    intro h1
    have : 2 ∣ m := dvd_of_mod_eq_zero h1
    contradiction
  have : m % 2 = 1 := by omega
  use m / 2
  omega

lemma le_sq_sub_one {p : ℕ} (h : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  have : ∃ k, p - 1 = k ∧ 2 ≤ k := ⟨p - 1, rfl, by omega⟩
  rcases this with ⟨k, hk, hk2⟩
  have : p = k + 1 := by omega
  subst this
  have : k + 1 ≤ k ^ 2 := by nlinarith
  exact this

lemma totient_bound_lemma (q : ℕ) : q ≤ 2 * q.totient ^ 2 ∧ (Odd q → q ≤ q.totient ^ 2) := by
  induction' q using Nat.strong_induction_on with q ih
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  if hq1 : q = 1 then
    subst hq1
    simp
  else
    have hq2 : 1 < q := by omega
    let p := q.minFac
    let m := q / p
    have hp_prime : p.Prime := minFac_prime hq1
    have h_pm : p * m = q := Nat.mul_div_cancel' (minFac_dvd q)
    have hm_lt : m < q := Nat.div_lt_self hq hp_prime.one_lt
    rcases ih m hm_lt with ⟨ih_m_even, ih_m_odd⟩
    by_cases h_pm_dvd : p ∣ m
    · have h_tot : q.totient = p * m.totient := by
        rw [← h_pm]
        exact totient_mul_of_prime_of_dvd hp_prime h_pm_dvd
      constructor
      · rw [h_tot]
        calc q = p * m := h_pm.symm
          _ ≤ p * (2 * m.totient ^ 2) := mul_le_mul_left p ih_m_even
          _ = 2 * p * m.totient ^ 2 := by ring
          _ ≤ 2 * p ^ 2 * m.totient ^ 2 := by
            gcongr
            nlinarith
          _ = 2 * (p * m.totient) ^ 2 := by ring
      · intro hq_odd
        have hp_odd : Odd p := Odd.of_mul_left (h_pm.symm ▸ hq_odd)
        have hm_odd : Odd m := Odd.of_mul_right (h_pm.symm ▸ hq_odd)
        rw [h_tot]
        calc q = p * m := h_pm.symm
          _ ≤ p * (m.totient ^ 2) := mul_le_mul_left p (ih_m_odd hm_odd)
          _ ≤ p ^ 2 * m.totient ^ 2 := by
            gcongr
            nlinarith
          _ = (p * m.totient) ^ 2 := by ring
    · have h_tot : q.totient = (p - 1) * m.totient := by
        rw [← h_pm]
        exact totient_mul_of_prime_of_not_dvd hp_prime h_pm_dvd
      constructor
      · rw [h_tot]
        by_cases hp2 : p = 2
        · have hm_odd : Odd m := by
            have h_not_dvd : ¬ 2 ∣ m := by
              have : p = 2 := hp2
              rwa [←this]
            exact odd_of_not_two_dvd h_not_dvd
          calc q = p * m := h_pm.symm
            _ = 2 * m := by rw [hp2]
            _ ≤ 2 * m.totient ^ 2 := mul_le_mul_left 2 (ih_m_odd hm_odd)
            _ = 2 * ( (2 - 1) * m.totient ) ^ 2 := by ring
            _ = 2 * ( (p - 1) * m.totient ) ^ 2 := by rw [hp2]
        · have hp_ge_2 : 2 ≤ p := hp_prime.two_le
          have hp3 : 3 ≤ p := by omega
          calc q = p * m := h_pm.symm
            _ ≤ p * (2 * m.totient ^ 2) := mul_le_mul_left p ih_m_even
            _ = 2 * p * m.totient ^ 2 := by ring
            _ ≤ 2 * (p - 1) ^ 2 * m.totient ^ 2 := by
              gcongr
              exact le_sq_sub_one hp3
            _ = 2 * ((p - 1) * m.totient) ^ 2 := by ring
      · intro hq_odd
        have hp_odd : Odd p := Odd.of_mul_left (h_pm.symm ▸ hq_odd)
        have hm_odd : Odd m := Odd.of_mul_right (h_pm.symm ▸ hq_odd)
        rw [h_tot]
        have hp_ge_2 : 2 ≤ p := hp_prime.two_le
        rcases hp_odd with ⟨k, hk⟩
        have hp3 : 3 ≤ p := by omega
        calc q = p * m := h_pm.symm
          _ ≤ p * m.totient ^ 2 := mul_le_mul_left p (ih_m_odd hm_odd)
          _ ≤ (p - 1) ^ 2 * m.totient ^ 2 := by
            gcongr
            exact le_sq_sub_one hp3
          _ = ((p - 1) * m.totient) ^ 2 := by ring
