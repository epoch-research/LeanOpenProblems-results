import FormalConjectures.Util.ProblemImports
open Nat

lemma factorial_gt_two_n_mul_two_n_plus_one {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial > 2 * n * (2 * n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial > 2 * m * (2 * m + 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) > (m + 1) * (2 * m * (2 * m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
    have h2 : (m + 1) * (2 * m * (2 * m + 1)) ≥ 2 * (m + 1) * (2 * (m + 1) + 1) := by
      have : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
      rw [this]
      have h3 : m * (2 * m + 1) ≥ 2 * m + 3 := by
        have h_mul : m * (2 * m + 1) = 2 * m * m + m := by ring
        rw [h_mul]
        have h_quad : 2 * m * m ≥ 10 * m := by
          calc 2 * m * m = (2 * m) * m := by ring
            _ ≥ (2 * 5) * m := Nat.mul_le_mul_right m (by omega)
            _ = 10 * m := by ring
        omega
      have h4 : 2 * (m + 1) * (m * (2 * m + 1)) ≥ 2 * (m + 1) * (2 * m + 3) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      have h_comm : (m + 1) * (2 * m * (2 * m + 1)) = 2 * (m + 1) * (m * (2 * m + 1)) := by ring
      rw [h_comm]
      exact h4
    exact lt_of_le_of_lt h2 h1


lemma factorial_gt_quadratic {n : ℕ} (hn : 4 ≤ n) : 2 * n.factorial > n * (n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_mul : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_mul]
    have h1 : 2 * m.factorial > m * (m + 1) := ih
    have h2 : (m + 1) * (2 * m.factorial) > (m + 1) * (m * (m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have h3 : m * (m + 1) ≥ m + 2 := by
      calc m * (m + 1) ≥ 4 * (m + 1) := Nat.mul_le_mul_right (m + 1) hm
        _ = 4 * m + 4 := by ring
        _ ≥ m + 2 := by omega
    have h4 : (m + 1) * (m * (m + 1)) ≥ (m + 1) * (m + 2) := Nat.mul_le_mul_left (m + 1) h3
    exact lt_of_le_of_lt h4 h2

lemma factorial_gt_two_n_mul {n : ℕ} (hn : 5 ≤ n) : 2 * n.factorial ≥ 2 * n * (2 * n - 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial ≥ 2 * m * (2 * m - 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) ≥ (m + 1) * (2 * m * (2 * m - 1)) := Nat.mul_le_mul_left (m + 1) ih'
    have h2 : (m + 1) * (2 * m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * (m + 1) - 1) := by
      have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [this]
      have h3 : m * (2 * m - 1) ≥ 2 * m + 1 := by
        have h_sub : m * (2 * m - 1) = 2 * m * m - m := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          congr 1
          ring
        rw [h_sub]
        have h_quad : 2 * m * m ≥ 10 * m := by
          calc 2 * m * m = (2 * m) * m := by ring
            _ ≥ (2 * 5) * m := Nat.mul_le_mul_right m (by omega)
            _ = 10 * m := by ring
        omega
      have h4 : 2 * (m + 1) * (m * (2 * m - 1)) ≥ 2 * (m + 1) * (2 * m + 1) := Nat.mul_le_mul_left (2 * (m + 1)) h3
      have h_comm : (m + 1) * (2 * m * (2 * m - 1)) = 2 * (m + 1) * (m * (2 * m - 1)) := by ring
      rw [h_comm]
      exact h4
    exact le_trans h2 h1

lemma k_ge_three_p {n k p : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (hp_gt : n / 2 < p) (hp_le : p ≤ n) (hn : 5 ≤ n) :
    k + 1 ≥ 3 * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨d, hd⟩ := hpk
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases lt_or_ge d 3 with hd_lt | hd_ge_3
    · interval_cases d
      · -- d = 1
        have hkp : k = p := by omega
        rw [hkp] at h_eq
        have hp_le_fact : p * (p + 1) ≤ n * (n + 1) := Nat.mul_le_mul hp_le (by omega)
        have h_gt : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
        omega
      · -- d = 2
        have hkp : k = 2 * p := by omega
        rw [hkp] at h_eq
        have hp_le_fact : 2 * p * (2 * p + 1) ≤ 2 * n * (2 * n + 1) := by
          have h2p : 2 * p ≤ 2 * n := by omega
          have h2p1 : 2 * p + 1 ≤ 2 * n + 1 := by omega
          exact Nat.mul_le_mul h2p h2p1
        have h_gt : 2 * n.factorial > 2 * n * (2 * n + 1) := factorial_gt_two_n_mul_two_n_plus_one (by omega)
        omega
    · have hk_ge : k ≥ 3 * p := by
        calc k = p * d := hd
          _ ≥ p * 3 := Nat.mul_le_mul_left p hd_ge_3
          _ = 3 * p := by ring
      omega
  · obtain ⟨d, hd⟩ := hpk1
    have hd_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases lt_or_ge d 3 with hd_lt | hd_ge_3
    · interval_cases d
      · -- d = 1
        have hkp : k + 1 = p := by omega
        have hk_eq : k = p - 1 := by omega
        rw [hk_eq] at h_eq
        have hp_eq : p - 1 + 1 = p := by omega
        rw [hp_eq] at h_eq
        have hp_le_fact : (p - 1) * p ≤ (n - 1) * n := by
          have h_p_pos : p > 0 := Nat.Prime.pos hp_prime
          have h_sub : p - 1 ≤ n - 1 := by omega
          exact Nat.mul_le_mul h_sub hp_le
        have h_gt : 2 * n.factorial > n * (n - 1) := by
          have h_gt_quad : 2 * n.factorial > n * (n + 1) := factorial_gt_quadratic (by omega)
          have h_quad_le : n * (n + 1) ≥ (n - 1) * n := by
            have : n + 1 ≥ n - 1 := by omega
            have h_mul_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
            rw [h_mul_comm]
            exact Nat.mul_le_mul_left n this
          omega
        have h_comm : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
        rw [h_comm] at hp_le_fact
        omega
      · -- d = 2
        have hkp : k + 1 = 2 * p := by omega
        have hk_eq : k = 2 * p - 1 := by omega
        rw [hk_eq] at h_eq
        have hp_eq : 2 * p - 1 + 1 = 2 * p := by omega
        rw [hp_eq] at h_eq
        have hp_le_fact : (2 * p - 1) * (2 * p) ≤ (2 * n - 1) * (2 * n) := by
          have h_sub : 2 * p - 1 ≤ 2 * n - 1 := by omega
          have h_le_2p : 2 * p ≤ 2 * n := by omega
          exact Nat.mul_le_mul h_sub h_le_2p
        have h_gt : 2 * n.factorial > (2 * n - 1) * (2 * n) := by
          have h_gt_plus : 2 * n.factorial > 2 * n * (2 * n + 1) := factorial_gt_two_n_mul_two_n_plus_one hn
          have h_ineq : 2 * n * (2 * n + 1) > 2 * n * (2 * n - 1) := by
            have : 2 * n + 1 > 2 * n - 1 := by omega
            exact Nat.mul_lt_mul_of_pos_left this (by omega)
          have h_comm : (2 * n - 1) * (2 * n) = 2 * n * (2 * n - 1) := Nat.mul_comm _ _
          rw [h_comm]
          omega
        have h_comm : (2 * p - 1) * (2 * p) = 2 * p * (2 * p - 1) := Nat.mul_comm _ _
        rw [h_comm] at h_eq
        omega
    · calc k + 1 = p * d := hd
        _ ≥ p * 3 := Nat.mul_le_mul_left p hd_ge_3
        _ = 3 * p := by ring


lemma k_ge_D_p {n k p D : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (hp_le : p ≤ n)
    (h_gt : 2 * n.factorial > (D - 1) * n * ((D - 1) * n + 1)) (hD : D ≥ 2) :
    k + 1 ≥ D * p := by
  have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  have hp_dvd_two_fact : p ∣ 2 * n.factorial := dvd_mul_of_dvd_right hp_dvd_fact 2
  rw [h_eq] at hp_dvd_two_fact
  cases' Nat.Prime.dvd_mul hp_prime |>.mp hp_dvd_two_fact with hpk hpk1
  · obtain ⟨a, ha⟩ := hpk
    have ha_pos : a > 0 := by
      by_contra hc
      have : a = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    rcases lt_or_ge a D with ha_lt | ha_ge
    · have ha_le : a ≤ D - 1 := by omega
      have hk_le : k * (k + 1) ≤ (D - 1) * n * ((D - 1) * n + 1) := by
        rw [ha]
        have h1 : p * a ≤ (D - 1) * n := by
          have : p * a ≤ n * (D - 1) := Nat.mul_le_mul hp_le ha_le
          rwa [Nat.mul_comm n (D - 1)] at this
        have h2 : p * a + 1 ≤ (D - 1) * n + 1 := by omega
        exact Nat.mul_le_mul h1 h2
      omega
    · have hk_ge : k ≥ D * p := by
        calc k = p * a := ha
          _ ≥ p * D := Nat.mul_le_mul_left p ha_ge
          _ = D * p := by ring
      omega
  · obtain ⟨b, hb⟩ := hpk1
    have hb_pos : b > 0 := by
      by_contra hc
      have : b = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    rcases lt_or_ge b D with hb_lt | hb_ge
    · have hb_le : b ≤ D - 1 := by omega
      have hk_le : k * (k + 1) ≤ (D - 1) * n * ((D - 1) * n + 1) := by
        have h_bp : k + 1 = b * p := by rw [Nat.mul_comm b p]; exact hb
        have hk_eq : k = b * p - 1 := by omega
        rw [h_bp, hk_eq]
        have h2 : b * p ≤ (D - 1) * n := Nat.mul_le_mul hb_le hp_le
        have h1 : b * p - 1 ≤ (D - 1) * n := by omega
        have h3 : (D - 1) * n ≤ (D - 1) * n + 1 := by omega
        have h4 : b * p ≤ (D - 1) * n + 1 := h2.trans h3
        exact Nat.mul_le_mul h1 h4
      omega
    · calc k + 1 = p * b := hb
        _ ≥ p * D := Nat.mul_le_mul_left p hb_ge
        _ = D * p := by ring



lemma two_pow_61_dvd_factorial_67 : 2^61 ∣ (67).factorial := by decide

lemma two_pow_61_dvd_factorial {n : ℕ} (hn : 67 ≤ n) : 2^61 ∣ n.factorial := by
  have h_dvd : (67).factorial ∣ n.factorial := Nat.factorial_dvd_factorial hn
  exact dvd_trans two_pow_61_dvd_factorial_67 h_dvd

lemma two_pow_62_dvd_two_factorial {n : ℕ} (hn : 67 ≤ n) : 2^62 ∣ 2 * n.factorial := by
  have h1 : 2^62 = 2 * 2^61 := by ring
  rw [h1]
  have h2 : 2^61 ∣ n.factorial := two_pow_61_dvd_factorial hn
  exact Nat.mul_dvd_mul_left 2 h2

lemma factorial_gt_huge {n : ℕ} (hn : 67 ≤ n) : 2 * n.factorial > (2^62 - 1) * n * ((2^62 - 1) * n + 1) := by
  induction' n, hn using Nat.le_induction with m hm ih
  · decide
  · have h_eq : 2 * (m + 1).factorial = (m + 1) * (2 * m.factorial) := by
      rw [factorial_succ]
      ring
    rw [h_eq]
    have ih' : 2 * m.factorial > (2^62 - 1) * m * ((2^62 - 1) * m + 1) := ih
    have h1 : (m + 1) * (2 * m.factorial) > (m + 1) * ((2^62 - 1) * m * ((2^62 - 1) * m + 1)) := by
      exact Nat.mul_lt_mul_of_pos_left ih' (by omega)
    have h2 : (m + 1) * ((2^62 - 1) * m * ((2^62 - 1) * m + 1)) ≥ (2^62 - 1) * (m + 1) * ((2^62 - 1) * (m + 1) + 1) := by
      -- we want (m + 1) * (2^62 - 1) * m * ((2^62 - 1) * m + 1) >= (2^62 - 1) * (m + 1) * ((2^62 - 1) * (m + 1) + 1)
      -- which is (2^62 - 1) * (m + 1) * (m * ((2^62 - 1) * m + 1)) >= (2^62 - 1) * (m + 1) * ((2^62 - 1) * (m + 1) + 1)
      have h_comm1 : (m + 1) * ((2^62 - 1) * m * ((2^62 - 1) * m + 1)) = (2^62 - 1) * (m + 1) * (m * ((2^62 - 1) * m + 1)) := by ring
      rw [h_comm1]
      have h3 : m * ((2^62 - 1) * m + 1) ≥ (2^62 - 1) * (m + 1) + 1 := by
        have h_mul1 : m * ((2^62 - 1) * m + 1) = (2^62 - 1) * m * m + m := by ring
        have h_mul2 : (2^62 - 1) * (m + 1) + 1 = (2^62 - 1) * m + 2^62 := by ring
        rw [h_mul1, h_mul2]
        have h_quad : (2^62 - 1) * m * m ≥ (2^62 - 1) * m + 2^62 := by
          calc (2^62 - 1) * m * m = ((2^62 - 1) * m) * m := by ring
            _ ≥ ((2^62 - 1) * m) * 67 := Nat.mul_le_mul_left _ hm
            _ = (2^62 - 1) * m * 1 + (2^62 - 1) * m * 66 := by ring
            _ ≥ (2^62 - 1) * m * 1 + (2^62 - 1) * 67 * 66 := by
              have : (2^62 - 1) * m * 66 ≥ (2^62 - 1) * 67 * 66 := by
                have : (2^62 - 1) * m ≥ (2^62 - 1) * 67 := Nat.mul_le_mul_left _ hm
                omega
              omega
            _ ≥ (2^62 - 1) * m + 2^62 := by
              -- (2^62-1)*67*66 is obviously >= 2^62
              have : (2^62 - 1) * 67 * 66 ≥ 2^62 := by
                -- since 2^62 - 1 >= 1 and 67*66 >= 4422, wait:
                -- (2^62-1)*67*66 = 4422 * 2^62 - 4422 >= 2^62
                -- we can show this by:
                calc (2^62 - 1) * 67 * 66 = 4422 * 2^62 - 4422 := by ring
                  _ ≥ 1 * 2^62 := by omega
              omega
        omega
      exact Nat.mul_le_mul_left _ h3
    exact lt_of_le_of_lt h2 h1


lemma coprime_dvd_mul {q c A B : ℕ} (hq : Nat.Prime q) (h_coprime : Nat.Coprime A B) (h_dvd : q^c ∣ A * B) :
  q^c ∣ A ∨ q^c ∣ B := by
  by_cases hqA : q ∣ A
  · left
    have hqB : ¬ q ∣ B := by
      intro hqB
      have h_div : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hqB
      rw [h_coprime.gcd_eq_one] at h_div
      exact Nat.Prime.not_dvd_one hq h_div
    have h_cop : Nat.Coprime (q^c) B := hq.coprime_iff_not_dvd.mpr hqB |>.pow_left c
    have h_dvd' : q^c ∣ B * A := by rw [Nat.mul_comm B A]; exact h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'
  · right
    have h_cop : Nat.Coprime (q^c) A := hq.coprime_iff_not_dvd.mpr hqA |>.pow_left c
    have h_dvd' : q^c ∣ A * B := h_dvd
    exact h_cop.dvd_of_dvd_mul_left h_dvd'

lemma two_pow_62_dvd_k_or_k_add_one {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 67 ≤ n) :
    2^62 ∣ k ∨ 2^62 ∣ k + 1 := by
  have h_dvd : 2^62 ∣ k * (k + 1) := by
    rw [← h_eq]
    exact two_pow_62_dvd_two_factorial hn
  have h_cop : Nat.Coprime k (k + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right k
  have h_prime : Nat.Prime 2 := Nat.prime_two
  exact coprime_dvd_mul h_prime h_cop h_dvd

lemma k_ge_two_pow_62 {n k : ℕ} (h_eq : 2 * n.factorial = k * (k + 1)) (hn : 67 ≤ n) :
    k + 1 ≥ 2^62 := by
  have h_cases : 2^62 ∣ k ∨ 2^62 ∣ k + 1 := two_pow_62_dvd_k_or_k_add_one h_eq hn
  rcases h_cases with ⟨y, hy⟩ | ⟨y, hy⟩
  · have hy_pos : y > 0 := by
      by_contra hc
      have : y = 0 := by omega
      subst this
      have hk0 : k = 0 := by omega
      rw [hk0] at h_eq
      simp at h_eq
      have h_fact_pos : n.factorial > 0 := Nat.factorial_pos n
      omega
    have hk_ge : k ≥ 2^62 := by
      calc k = 2^62 * y := hy
        _ ≥ 2^62 * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = 2^62 := by ring
    omega
  · have hy_pos : y > 0 := by
      by_contra hc
      have : y = 0 := by omega
      subst this
      have hk1 : k + 1 = 0 := by omega
      omega
    calc k + 1 = 2^62 * y := hy
      _ ≥ 2^62 * 1 := Nat.mul_le_mul_left _ (by omega)
      _ = 2^62 := by ring



