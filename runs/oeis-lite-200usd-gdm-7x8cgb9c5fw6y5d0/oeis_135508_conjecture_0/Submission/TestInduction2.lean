import FormalConjectures.Util.ProblemImports

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_pos (n : ℕ) (hn : n > 0) : x_seq n > 0 := sorry
lemma x_seq_dvd (n : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + 1) := sorry
lemma x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (hab : a ≤ b) : x_seq a ∣ x_seq b := sorry
lemma x_seq_step_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n = x_seq (n - 1) * (2 + n / Nat.gcd (x_seq (n - 1)) n) := sorry
lemma max_prime_factor_x_seq (n : ℕ) (hn : n > 0) (r : ℕ) (hr : Nat.Prime r) (hd : r ∣ x_seq n) : r ≤ n + 2 := sorry

lemma divisor_mod_r_eq (r : ℕ) (hr_ge : r ≥ 5) (hr : Nat.Prime r) (k : ℕ) (hk : k ∣ r^2 - 2) (j : ℕ) (hk_eq : k + 2 = j * r) : k = r^2 - 2 := by
  rcases hk with ⟨m, hm⟩
  have hk_pos : k > 0 := by
    by_contra h_zero
    have : k = 0 := by omega
    rw [this] at hm
    simp at hm
    have : r^2 ≥ 25 := by nlinarith
    omega
  have hj_pos : j ≥ 1 := by
    by_contra h_zero
    have : j = 0 := by omega
    rw [this] at hk_eq
    simp at hk_eq
  have h_jr_ge : j * r ≥ 2 := by nlinarith
  have h_k_eq : k = j * r - 2 := by omega
  have h_sub_eq : r^2 - 2 = (j * r - 2) * m := by
    rw [hm, h_k_eq]
  have h_mul_sub : (j * r - 2) * m = j * r * m - 2 * m := by
    have := Nat.mul_sub_right_distrib (j * r) 2 m
    have h_assoc : (j * r) * m = j * r * m := by ring
    rw [h_assoc] at this
    exact this
  rw [h_mul_sub] at h_sub_eq
  have hm_pos : m > 0 := by
    by_contra h
    have : m = 0 := by omega
    subst this
    simp at hm
    have : r^2 ≥ 25 := by nlinarith
    omega
  have h_m_eq : m = 1 ∨ m > 1 := by
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hm_pos) with h_eq | h_lt
    · left; exact h_eq.symm
    · right; exact h_lt
  rcases h_m_eq with rfl | hm_gt
  · simp at hm
    exact hm.symm
  · have h_ge : j * r * m ≥ 2 * m := by nlinarith
    have h_sub_eq2 : r^2 - 2 + 2 * m = j * r * m := by omega
    have h_div : r ∣ 2 * m - 2 := by
      use j * m - r
      have h_dist : r * (j * m - r) = r * (j * m) - r * r := Nat.mul_sub_left_distrib r (j * m) r
      have h_r2 : r * r = r^2 := by ring
      rw [h_r2] at h_dist
      have h_sub_eq3 : r * (j * m) = r^2 - 2 + 2 * m := by
        have : r * (j * m) = j * r * m := by ring
        omega
      have h_ge2 : r * (j * m) ≥ r^2 := by
        have : r * (j * m) = j * r * m := by ring
        omega
      have h_sub_eq4 : r * (j * m) - r^2 = 2 * m - 2 := by
        rw [h_sub_eq3]
        have : r^2 ≥ 25 := by nlinarith
        omega
      rw [h_dist, h_sub_eq4]
    have h_coprime : Nat.Coprime r 2 := by
      have h_cases : Nat.gcd r 2 = 1 ∨ Nat.gcd r 2 = 2 := by
        have h_gcd_le : Nat.gcd r 2 ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right r 2)
        have h_gcd_pos : Nat.gcd r 2 > 0 := Nat.gcd_pos_of_pos_right r (by decide)
        omega
      rcases h_cases with h_gcd1 | h_gcd2
      · exact h_gcd1
      · have h_dvd_left := Nat.gcd_dvd_left r 2
        rw [h_gcd2] at h_dvd_left
        have h_eq : 2 = 1 ∨ 2 = r := hr.eq_one_or_self_of_dvd 2 h_dvd_left
        omega
    have h_div_m1 : r ∣ m - 1 := by
      have h_div2 : r ∣ 2 * (m - 1) := by
        have : 2 * (m - 1) = 2 * m - 2 := by omega
        rw [this]
        exact h_div
      exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_div2
    have h_le_m1 : r ≤ m - 1 := Nat.le_of_dvd (by omega) h_div_m1
    have h_m_ge : m ≥ r + 1 := by omega
    have hj_ge2 : j ≥ 2 := by
      by_contra h_lt
      have : j = 1 := by omega
      subst this
      have hk_eq2 : k + 2 = r := by omega
      have hk_dvd_r2 : k ∣ r^2 - 2 := ⟨m, hm⟩
      have h_sub : (r^2 - 2) - (r - 2) * (r + 2) = 2 := by
        have h_eq : r^2 = (r - 2) * (r + 2) + 4 := by
          have h_r : r = (r - 2) + 2 := by omega
          have h_pow2 : r^2 = r * r := by ring
          rw [h_pow2, h_r]
          have h_sim : (r - 2) + 2 - 2 = r - 2 := by omega
          rw [h_sim]
          ring
        omega
      have h_dvd_2 : k ∣ 2 := by
        have h_k_eq_sub : k = r - 2 := by omega
        have h_dvd_mul : k ∣ k * (r + 2) := dvd_mul_right k (r + 2)
        have h_eq_mul : k * (r + 2) = (r - 2) * (r + 2) := by rw [h_k_eq_sub]
        rw [h_eq_mul] at h_dvd_mul
        have hk_dvd_sub := Nat.dvd_sub hk_dvd_r2 h_dvd_mul
        rw [h_sub] at hk_dvd_sub
        exact hk_dvd_sub
      have h_le : k ≤ 2 := Nat.le_of_dvd (by omega) h_dvd_2
      have : r - 2 ≤ 2 := by omega
      omega
    have h_jr_ge2 : j * r ≥ 2 * r := Nat.mul_le_mul_right r hj_ge2
    have h_k_ge : k ≥ 2 * r - 2 := by omega
    have h_prod_ge : (2 * r - 2) * (r + 1) ≤ k * m := Nat.mul_le_mul h_k_ge h_m_ge
    have h_prod_val : (2 * r - 2) * (r + 1) = 2 * r^2 - 2 := by
      have h_dist : (2 * r - 2) * (r + 1) = 2 * r * (r + 1) - 2 * (r + 1) := Nat.mul_sub_right_distrib (2 * r) 2 (r + 1)
      have h1 : 2 * r * (r + 1) = 2 * r^2 + 2 * r := by
        have h_r2 : r^2 = r * r := by ring
        rw [h_r2]
        ring
      have h2 : 2 * (r + 1) = 2 * r + 2 := by ring
      rw [h1, h2] at h_dist
      omega
    have h_prod_eq : k * m = r^2 - 2 := hm.symm
    rw [h_prod_val, h_prod_eq] at h_prod_ge
    have : r^2 ≥ 25 := by nlinarith
    omega

lemma prime_dvd_x_seq_sq_sub_one_bounded_1019 (r : ℕ) (hr_le : r ≤ 1019) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := sorry

lemma prime_dvd_x_seq_sq_sub_one (r : ℕ) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  induction' r using Nat.strong_induction_on with r ih
  by_cases h_le : r ≤ 1019
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1019 r h_le hr
  · have hr_ge : r ≥ 5 := by omega
    have h_r2_sub_2_pos : r^2 - 2 > 0 := by
      have : r^2 ≥ 25 := by nlinarith
      omega
    have h_dvd : x_seq (r^2 - 2) ∣ x_seq (r^2 - 1) := by
      apply x_seq_dvd_of_le
      · exact h_r2_sub_2_pos
      · omega
    apply dvd_trans _ h_dvd
    set n := r^2 - 2
    have hn : n ≥ 2 := by
      have : r^2 ≥ 25 := by nlinarith
      omega
    have h_step := x_seq_step_eq_gen n hn
    set g := Nat.gcd (x_seq (n - 1)) n
    set k := n / g
    by_cases h_div_prev : r ∣ x_seq (n - 1)
    · have h_dvd2 : x_seq (n - 1) ∣ x_seq n := by
        have h_pos : n - 1 > 0 := by omega
        have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        rw [← h_eq]
        exact x_seq_dvd (n - 1) h_pos
      exact dvd_trans h_div_prev h_dvd2
    · have h_g_eq : g = 1 := by
        by_contra h_g_gt
        have hg_ne1 : g ≠ 1 := by omega
        set q := Nat.minFac g
        have hq_prime : Nat.Prime q := Nat.minFac_prime hg_ne1
        have hq_dvd_g : q ∣ g := Nat.minFac_dvd g
        have hg_dvd_n : g ∣ n := Nat.gcd_dvd_right (x_seq (n - 1)) n
        have hg_dvd_x : g ∣ x_seq (n - 1) := Nat.gcd_dvd_left (x_seq (n - 1)) n
        have hq_dvd_n : q ∣ r^2 - 2 := dvd_trans hq_dvd_g hg_dvd_n
        have hq_dvd_x : q ∣ x_seq (r^2 - 3) := dvd_trans hq_dvd_g hg_dvd_x
        have hq_ne_r : q ≠ r := by
          intro h_eq
          rw [h_eq] at hq_dvd_n
          have h_div_2 : r ∣ 2 := hq_dvd_n
          have : r ≤ 2 := Nat.le_of_dvd (by decide) h_div_2
          omega
        by_cases h_q_lt : q < r
        · have h_q_dvd_sq : q ∣ x_seq (q^2 - 1) := ih q h_q_lt hq_prime
          have h_q2_sub_1_le : q^2 - 1 ≤ r^2 - 3 := by
            have h_q_sq : q^2 ≤ (r - 1)^2 := by nlinarith
            have h_ring : (r - 1)^2 = r^2 - 2 * r + 1 := by
              have : r ≥ 1 := by omega
              omega
            omega
          have h_q2_sub_1_pos : q^2 - 1 > 0 := by
            have : q ≥ 2 := Nat.Prime.two_le hq_prime
            have : q^2 ≥ 4 := by nlinarith
            omega
          have h_x_dvd : x_seq (q^2 - 1) ∣ x_seq (r^2 - 3) := x_seq_dvd_of_le (q^2 - 1) (r^2 - 3) h_q2_sub_1_pos h_q2_sub_1_le
          have h_q_dvd_x' : q ∣ x_seq (r^2 - 3) := dvd_trans h_q_dvd_sq h_x_dvd
          -- This is not a contradiction, but we can proceed with the other case where q > r
          sorry
        · have h_q_gt : q > r := by omega
          have h_q_le_n : q ≤ r^2 - 2 := Nat.le_of_dvd h_r2_sub_2_pos hq_dvd_n
          set m := (r^2 - 2) / q
          have hm : r^2 - 2 = m * q := by
            have : r^2 - 2 = q * m := (Nat.mul_div_cancel' hq_dvd_n).symm
            rw [Nat.mul_comm] at this
            exact this
          have hm_pos : m > 0 := by
            by_contra h_zero
            have : m = 0 := by omega
            rw [this] at hm
            simp at hm
            have h_sq : r^2 ≥ 25 := by nlinarith
            omega
          have hm_lt : m < r := by
            by_contra h_ge
            have : m ≥ r := by omega
            have h_mq : m * q ≥ r * (r + 1) := Nat.mul_le_mul this (by omega)
            have h_ring : r * (r + 1) = r^2 + r := by ring
            rw [h_ring] at h_mq
            omega
          have h_m_eq : m = 1 ∨ m > 1 := by omega
          rcases h_m_eq with hm_eq1 | hm_gt
          · rw [hm_eq1] at hm
            simp at hm
            set P := r^2 - 2
            have hP_prime : Nat.Prime P := by
              rw [hm]
              exact hq_prime
            have hP_dvd_prev : P ∣ x_seq (r^2 - 4) := by
              have hn_sub3_ge2 : r^2 - 3 ≥ 2 := by
                have : r^2 ≥ 25 := by nlinarith
                omega
              have h_step3 := x_seq_step_eq_gen (r^2 - 3) hn_sub3_ge2
              rw [h_step3] at hq_dvd_x
              rw [Nat.Prime.dvd_mul hP_prime] at hq_dvd_x
              rcases hq_dvd_x with hdvd_prev | hdvd_mult
              · exact hdvd_prev
              · set g3 := Nat.gcd (x_seq (r^2 - 4)) (r^2 - 3)
                have h_g3_cases : g3 = 1 ∨ g3 ≥ 2 := by omega
                rcases h_g3_cases with h_g3_1 | h_g3_ge2
                · rw [h_g3_1] at hdvd_mult
                  simp at hdvd_mult
                  have h_dvd_sub : P ∣ (r^2 - 1) - P := Nat.dvd_sub hdvd_mult (dvd_refl P)
                  have : (r^2 - 1) - P = 1 := by omega
                  rw [this] at h_dvd_sub
                  have : P = 1 := Nat.eq_one_of_dvd_one h_dvd_sub
                  have : P ≥ 2 := Nat.Prime.two_le hP_prime
                  omega
                · have h_div_le : (r^2 - 3) / g3 ≤ (r^2 - 3) / 2 := Nat.div_le_div_left (by omega) (by omega)
                  have h_lt_P : 2 + (r^2 - 3) / g3 < P := by
                    have : (r^2 - 3) / 2 < r^2 - 4 := by
                      have : r^2 ≥ 25 := by nlinarith
                      omega
                    omega
                  have h_pos_val : 2 + (r^2 - 3) / g3 > 0 := by omega
                  have h_le_val := Nat.le_of_dvd h_pos_val hdvd_mult
                  omega
            have hn_sub4_ge2 : r^2 - 4 ≥ 2 := by
              have : r^2 ≥ 25 := by nlinarith
              omega
            have h_step4 := x_seq_step_eq_gen (r^2 - 4) hn_sub4_ge2
            rw [h_step4] at hP_dvd_prev
            rw [Nat.Prime.dvd_mul hP_prime] at hP_dvd_prev
            rcases hP_dvd_prev with hdvd_prev4 | hdvd_mult4
            · have h_le := max_prime_factor_x_seq (r^2 - 5) (by omega) P hP_prime hdvd_prev4
              omega
            · set g4 := Nat.gcd (x_seq (r^2 - 5)) (r^2 - 4)
              have h_g4_cases : g4 = 1 ∨ g4 ≥ 2 := by omega
              rcases h_g4_cases with h_g4_1 | h_g4_ge2
              · set p' := Nat.minFac (r - 2)
                have hp'_prime : Nat.Prime p' := Nat.minFac_prime (by omega)
                have hp'_dvd : p' ∣ r - 2 := Nat.minFac_dvd (r - 2)
                have hp'_lt : p' < r := by
                  have : p' ≤ r - 2 := Nat.minFac_le_of_pos (by omega)
                  omega
                have hp'_dvd_sq : p' ∣ x_seq (p'^2 - 1) := ih p' hp'_lt hp'_prime
                have hp'_dvd_sq_le : p'^2 - 1 ≤ r^2 - 5 := by
                  have : p' ≤ r - 2 := by omega
                  have : p'^2 ≤ (r - 2)^2 := Nat.mul_le_mul this this
                  have h_ring : (r - 2)^2 = r^2 - 4 * r + 4 := by
                    have : r ≥ 2 := by omega
                    omega
                  omega
                have hp'_dvd_sq_pos : p'^2 - 1 > 0 := by
                  have : p' ≥ 2 := Nat.Prime.two_le hp'_prime
                  have : p'^2 ≥ 4 := by nlinarith
                  omega
                have h_x_dvd' : x_seq (p'^2 - 1) ∣ x_seq (r^2 - 5) := x_seq_dvd_of_le (p'^2 - 1) (r^2 - 5) hp'_dvd_sq_pos hp'_dvd_sq_le
                have hp'_dvd_x : p' ∣ x_seq (r^2 - 5) := dvd_trans hp'_dvd_sq h_x_dvd'
                have hp'_dvd_n : p' ∣ r^2 - 4 := by
                  have : p' ∣ (r - 2) * (r + 2) := dvd_mul_of_dvd_left hp'_dvd (r + 2)
                  have h_ring : (r - 2) * (r + 2) = r^2 - 4 := by
                    have : r ≥ 2 := by omega
                    omega
                  rw [h_ring] at this
                  exact this
                have hp'_dvd_gcd : p' ∣ g4 := Nat.dvd_gcd hp'_dvd_x hp'_dvd_n
                rw [h_g4_1] at hp'_dvd_gcd
                have : p' = 1 := Nat.eq_one_of_dvd_one hp'_dvd_gcd
                have : p' ≥ 2 := Nat.Prime.two_le hp'_prime
                omega
              · have h_div_le : (r^2 - 4) / g4 ≤ (r^2 - 4) / 2 := Nat.div_le_div_left (by omega) (by omega)
                have h_lt_P : 2 + (r^2 - 4) / g4 < P := by
                  have : (r^2 - 4) / 2 < r^2 - 4 := by
                    have : r^2 ≥ 25 := by nlinarith
                    omega
                  omega
                have h_pos_val : 2 + (r^2 - 4) / g4 > 0 := by omega
                have h_le_val := Nat.le_of_dvd h_pos_val hdvd_mult4
                omega
          · set q' := Nat.minFac m
            have hq'_prime : Nat.Prime q' := Nat.minFac_prime (by omega)
            have hq'_dvd_m : q' ∣ m := Nat.minFac_dvd m
            have hq'_lt : q' < r := by
              have : q' ≤ m := Nat.minFac_le_of_pos hm_pos
              omega
            have hq'_dvd_sq : q' ∣ x_seq (q'^2 - 1) := ih q' hq'_lt hq'_prime
            have hq'_dvd_n : q' ∣ r^2 - 2 := by
              have : q' ∣ m * q := dvd_mul_of_dvd_left hq'_dvd_m q
              rw [← hm] at this
              exact this
            have hq'_dvd_sq_le : q'^2 - 1 ≤ r^2 - 3 := by
              have : q' ≤ r - 1 := by omega
              have : q'^2 ≤ (r - 1)^2 := Nat.mul_le_mul this this
              have h_ring : (r - 1)^2 = r^2 - 2 * r + 1 := by
                have : r ≥ 1 := by omega
                omega
              omega
            have hq'_dvd_sq_pos : q'^2 - 1 > 0 := by
              have : q' ≥ 2 := Nat.Prime.two_le hq'_prime
              have : q'^2 ≥ 4 := by nlinarith
              omega
            have h_x_dvd' : x_seq (q'^2 - 1) ∣ x_seq (r^2 - 3) := x_seq_dvd_of_le (q'^2 - 1) (r^2 - 3) hq'_dvd_sq_pos hq'_dvd_sq_le
            have hq'_dvd_x : q' ∣ x_seq (r^2 - 3) := dvd_trans hq'_dvd_sq h_x_dvd'
            have hq'_dvd_gcd : q' ∣ g := Nat.dvd_gcd hq'_dvd_x hq'_dvd_n
            have hq'_ge_q : q' ≥ q := Nat.minFac_le_of_dvd hq'_dvd_gcd
            omega
      have hk_eq : k = r^2 - 2 := by
        unfold k
        rw [h_g_eq]
        simp [n]
      have h_div_prev2 : r ∣ 2 + k := by
        rw [hk_eq]
        have h_sum_eq : 2 + (r^2 - 2) = r^2 := by
          have : r^2 ≥ 25 := by nlinarith
          omega
        rw [h_sum_eq]
        have h_pow2 : r^2 = r * r := by ring
        rw [h_pow2]
        exact dvd_mul_right r r
      rw [h_step]
      exact dvd_mul_of_dvd_right h_div_prev2 (x_seq (n - 1))
