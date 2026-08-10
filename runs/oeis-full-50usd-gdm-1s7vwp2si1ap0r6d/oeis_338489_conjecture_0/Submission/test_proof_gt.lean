import FormalConjectures.Util.ProblemImports
open Nat

lemma k_mul_k_add_one_even (k : ℕ) : 2 ∣ k * (k + 1) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · use m * (2 * m + 1)
    ring
  · use (2 * m + 1) * (m + 1)
    ring

lemma k_mul_k_add_one_div_two_mul_two (k : ℕ) : (k * (k + 1) / 2) * 2 = k * (k + 1) := by
  have hdvd : 2 ∣ k * (k + 1) := k_mul_k_add_one_even k
  exact Nat.div_mul_cancel hdvd

lemma exists_prime_div_factorial (n : ℕ) (hn : 6 ≤ n) : ∃ p, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by
  have h_pos : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) h_pos
  use p
  refine ⟨hp_prime, hp1, ?_⟩
  have h_le : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  exact hp2.trans h_le

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

lemma k_ge_D_p {n k p D : ℕ} (h_eq : 2 * n.factorial = k * (k + 1))
    (hp_prime : Nat.Prime p) (hp_le : p ≤ n)
    (h_gt : 2 * n.factorial > (D - 1) * n * ((D - 1) * n + 1)) :
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
              have : (2^62 - 1) * 67 * 66 ≥ 2^62 := by
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

lemma prime_factor_of_8_factorial_add_one {n : ℕ} (hn : 2 ≤ n) (y : ℕ) (hy : y * y = 8 * n.factorial + 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ y ∧ q > n := by
  have hy_gt_1 : y > 1 := by
    by_contra hc
    have : y = 0 ∨ y = 1 := by omega
    rcases this with rfl | rfl
    · have : n.factorial > 0 := Nat.factorial_pos n
      omega
    · have : n.factorial > 0 := Nat.factorial_pos n
      omega
  have hy_ne1 : y ≠ 1 := by omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hy_ne1
  use q
  refine ⟨hq_prime, hq_dvd, ?_⟩
  by_contra hc
  have hq_le : q ≤ n := by omega
  have hq_dvd_fact : q ∣ n.factorial := Nat.dvd_factorial (Nat.Prime.pos hq_prime) hq_le
  have hq_dvd_8_fact : q ∣ 8 * n.factorial := dvd_mul_of_dvd_right hq_dvd_fact 8
  have hq_dvd_y2 : q ∣ y * y := by
    have : y * y = y^2 := by ring
    rw [this]
    exact dvd_pow hq_dvd (by omega)
  rw [hy] at hq_dvd_y2
  have hq_dvd_1 : q ∣ 1 := (Nat.dvd_add_right hq_dvd_8_fact).mp hq_dvd_y2
  have : q = 1 := Nat.dvd_one.mp hq_dvd_1
  subst this
  exact Nat.Prime.ne_one hq_prime rfl

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

lemma not_triangular_of_ge_67 {n : ℕ} (hn : 67 ≤ n) : ¬ (∃ k : ℕ, n.factorial = k * (k + 1) / 2) := by
  sorry
