import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 500000
set_option maxHeartbeats 1000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_pos (n : ℕ) (hn : n > 0) : x_seq n > 0 := by
  induction' n with n ih
  · contradiction
  · cases' n with n'
    · simp [x_seq]
    · rw [x_seq]
      · have h1 : n' + 1 > 0 := by omega
        have h2 : x_seq (n' + 1) > 0 := ih h1
        omega
      · omega

lemma div_add_rule (a b c : ℕ) (ha : a > 0) : (a * b + c) / a = b + c / a := by
  have h_mul : a * b = b * a := Nat.mul_comm a b
  have h1 : a * b + c = c + b * a := by rw [h_mul, Nat.add_comm]
  have h2 : b + c / a = c / a + b := Nat.add_comm b (c / a)
  rw [h1, h2]
  exact Nat.add_mul_div_right c b ha

lemma lcm_def_eq (m n : ℕ) : Nat.lcm m n = m * n / Nat.gcd m n := rfl

lemma lcm_div_rule (a b : ℕ) (ha : a > 0) : Nat.lcm a b / a = b / Nat.gcd a b := by
  rw [lcm_def_eq, Nat.div_div_eq_div_mul]
  have h_comm : Nat.gcd a b * a = a * Nat.gcd a b := Nat.mul_comm _ _
  rw [h_comm]
  exact Nat.mul_div_mul_left b (Nat.gcd a b) ha

lemma x_seq_dvd (n : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n
  · contradiction
  · rename_i n'
    nth_rw 2 [x_seq]
    · have h1 : x_seq (n' + 1) ∣ 2 * x_seq (n' + 1) := dvd_mul_left _ _
      have h2 : x_seq (n' + 1) ∣ Nat.lcm (x_seq (n' + 1)) (n' + 1 + 1) := Nat.dvd_lcm_left _ _
      exact dvd_add h1 h2
    · omega

lemma x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (hab : a ≤ b) : x_seq a ∣ x_seq b := by
  induction' h : b - a with k ih generalizing a b
  · have : a = b := by omega
    rw [this]
  · have hab_lt : a < b := by omega
    have h_prev : x_seq a ∣ x_seq (b - 1) := by
      apply ih a (b - 1)
      · omega
      · omega
      · omega
    have h_step : x_seq (b - 1) ∣ x_seq b := by
      have h_b1_pos : b - 1 > 0 := by omega
      have h_eq : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
      rw [← h_eq]
      exact x_seq_dvd (b - 1) h_b1_pos
    exact dvd_trans h_prev h_step

lemma gcd_prime_eq (a p : ℕ) (hp : Nat.Prime p) : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := by
  apply hp.eq_one_or_self_of_dvd
  exact Nat.gcd_dvd_right a p

lemma x_seq_div_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n / x_seq (n - 1) = 2 + n / Nat.gcd (x_seq (n - 1)) n := by
  have h_cancel : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have h_pos : x_seq (n - 1) > 0 := by
    apply x_seq_pos
    omega
  have h_x_seq_n : x_seq n = 2 * x_seq (n - 1) + Nat.lcm (x_seq (n - 1)) n := by
    have h_step : x_seq (n - 1 + 1) = 2 * x_seq (n - 1) + Nat.lcm (x_seq (n - 1)) (n - 1 + 1) := by
      rw [x_seq]
      omega
    rw [h_cancel] at h_step
    exact h_step
  rw [h_x_seq_n]
  have h_comm_mul : 2 * x_seq (n - 1) = x_seq (n - 1) * 2 := Nat.mul_comm _ _
  rw [h_comm_mul]
  rw [div_add_rule (x_seq (n - 1)) 2 (Nat.lcm (x_seq (n - 1)) n) h_pos]
  rw [lcm_div_rule (x_seq (n - 1)) n h_pos]

lemma x_seq_step_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n = x_seq (n - 1) * (2 + n / Nat.gcd (x_seq (n - 1)) n) := by
  have h_dvd : x_seq (n - 1) ∣ x_seq n := by
    have h_pos : n - 1 > 0 := by omega
    have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    rw [← h_eq]
    exact x_seq_dvd (n - 1) h_pos
  have h_pos : x_seq (n - 1) > 0 := by
    apply x_seq_pos
    omega
  rw [← Nat.mul_div_cancel' h_dvd]
  rw [x_seq_div_eq_gen n hn]

lemma max_prime_factor_x_seq (n : ℕ) (hn : n > 0) (r : ℕ) (hr : Nat.Prime r) (hd : r ∣ x_seq n) : r ≤ n + 2 := by
  induction' n with n ih generalizing r
  · contradiction
  · cases' n with n'
    · simp [x_seq] at hd
      have : r ≥ 2 := Nat.Prime.two_le hr
      omega
    · have h_step := x_seq_step_eq_gen (n' + 2) (by omega)
      rw [h_step] at hd
      rw [Nat.Prime.dvd_mul hr] at hd
      rcases hd with hd1 | hd2
      · have : r ≤ n' + 1 + 2 := ih (by omega) r hr hd1
        omega
      · have h_div_le : (n' + 2) / Nat.gcd (x_seq (n' + 1)) (n' + 2) ≤ n' + 2 := Nat.div_le_self _ _
        have h_div_ge : (n' + 2) / Nat.gcd (x_seq (n' + 1)) (n' + 2) ≥ 0 := Nat.zero_le _
        have h_le_add : r ≤ 2 + (n' + 2) / Nat.gcd (x_seq (n' + 1)) (n' + 2) := Nat.le_of_dvd (by omega) hd2
        omega

lemma prime_not_dvd_add (p h : ℕ) (hp : Nat.Prime p) (hp3 : p > 3) (hh : h ∣ p - 1) : ¬ p ∣ 2 + h := by
  intro h_dvd
  have h_le : h ≤ p - 1 := Nat.le_of_dvd (by omega) hh
  have h_p_le : p ≤ 2 + h := Nat.le_of_dvd (by omega) h_dvd
  have h_eq_or : 2 + h = p ∨ 2 + h = p + 1 := by omega
  rcases h_eq_or with h_eq | h_eq
  · have : h = p - 2 := by omega
    rw [this] at hh
    have h_dvd_sub : p - 2 ∣ (p - 1) - (p - 2) := Nat.dvd_sub hh (dvd_refl _)
    have h_sub_eq : (p - 1) - (p - 2) = 1 := by omega
    rw [h_sub_eq] at h_dvd_sub
    have : p - 2 = 1 := Nat.eq_one_of_dvd_one h_dvd_sub
    omega
  · have h_dvd_1 : p ∣ (p + 1) - p := by
      have h_eq' : 2 + h = p + 1 := h_eq
      rw [h_eq'] at h_dvd
      have h_refl : p ∣ p := dvd_refl p
      exact Nat.dvd_sub h_dvd h_refl
    have h_sub_eq : (p + 1) - p = 1 := by omega
    rw [h_sub_eq] at h_dvd_1
    have hp1 : p = 1 := Nat.eq_one_of_dvd_one h_dvd_1
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    omega

lemma prime_not_dvd_x_seq_small (p : ℕ) (hp_lt : p < 600) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  revert hp hp2 hp_lt p
  decide

lemma prime_dvd_x_seq_sq_sub_one_bounded (r : ℕ) (hr_lt : r < 15) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  revert hr hr_lt r
  decide

lemma dvd_17 : 17 ∣ x_seq (17^2 - 1) := by decide
lemma dvd_19 : 19 ∣ x_seq (19^2 - 1) := by decide
lemma dvd_23 : 23 ∣ x_seq (23^2 - 1) := by decide
lemma dvd_29 : 29 ∣ x_seq (29^2 - 1) := by decide
lemma dvd_31 : 31 ∣ x_seq (31^2 - 1) := by decide

lemma prime_dvd_x_seq_sq_sub_one_bounded_31 (r : ℕ) (hr_le : r ≤ 31) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h : r < 15
  · exact prime_dvd_x_seq_sq_sub_one_bounded r h hr
  · have hr_cases : r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 29 ∨ r = 31 := by
      have : r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (by decide : ¬ Nat.Prime 15) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 16) hr |>.elim
      · left; rfl
      · exact (by decide : ¬ Nat.Prime 18) hr |>.elim
      · right; left; rfl
      · exact (by decide : ¬ Nat.Prime 20) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 21) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 22) hr |>.elim
      · right; right; left; rfl
      · exact (by decide : ¬ Nat.Prime 24) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 25) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 26) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 27) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 28) hr |>.elim
      · right; right; right; left; rfl
      · exact (by decide : ¬ Nat.Prime 30) hr |>.elim
      · right; right; right; right; rfl
    rcases hr_cases with rfl | rfl | rfl | rfl | rfl
    · exact dvd_17
    · exact dvd_19
    · exact dvd_23
    · exact dvd_29
    · exact dvd_31

lemma prime_not_dvd_x_seq (p : ℕ) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  by_cases hp_lt : p < 600
  · exact prime_not_dvd_x_seq_small p hp_lt hp hp2
  · have hp_ge : p ≥ 600 := by omega
    have hq_pos : p - 2 > 0 := by omega
    have h_gcd_or := gcd_prime_eq (x_seq (p - 1)) p hp
    rcases h_gcd_or with h_gcd | h_gcd
    · exact h_gcd
    · have h_dvd : p ∣ x_seq (p - 1) := by
        have h_gcd_dvd := Nat.gcd_dvd_left (x_seq (p - 1)) p
        rw [h_gcd] at h_gcd_dvd
        exact h_gcd_dvd
      have h_step1 := x_seq_step_eq_gen (p - 1) (by omega)
      rw [h_step1] at h_dvd
      rw [Nat.Prime.dvd_mul hp] at h_dvd
      rcases h_dvd with h_dvd1 | h_dvd2
      · have h_eq_sub : p - 1 - 1 = p - 2 := by omega
        rw [h_eq_sub] at h_dvd1
        have h_step2 := x_seq_step_eq_gen (p - 2) (by omega)
        rw [h_step2] at h_dvd1
        rw [Nat.Prime.dvd_mul hp] at h_dvd1
        rcases h_dvd1 with h_dvd3 | h_dvd4
        · have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp h_dvd3
          omega
        · clear h_step1 h_step2
          set g := Nat.gcd (x_seq (p - 3)) (p - 2)
          have hg_dvd : g ∣ p - 2 := Nat.gcd_dvd_right _ _
          have hg_cases : g = 1 ∨ g > 1 := by
            clear h_dvd4
            omega
          rcases hg_cases with hg_eq1 | hg_gt1
          · clear h_dvd4
            have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
            set r := Nat.minFac (p - 2)
            have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
            have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
            have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
            have hr_le_23 : r ≤ 23 := by
              by_contra h_gt
              have : r ≥ 24 := by omega
              have : r^2 ≥ 576 := by nlinarith
              omega
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_23 r hr_le_23 hr_prime
            have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
            have h_r2_sub_1_pos : r^2 - 1 > 0 := by
              have : r ≥ 2 := Nat.Prime.two_le hr_prime
              nlinarith
            have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
            have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
            have h_r_dvd_gcd : r ∣ g := Nat.dvd_gcd h_r_dvd_x hr_dvd
            rw [hg_eq1] at h_r_dvd_gcd
            have : r ∣ 1 := h_r_dvd_gcd
            have : r = 1 := Nat.eq_one_of_dvd_one this
            have : r ≥ 2 := Nat.Prime.two_le hr_prime
            omega
          · -- g > 1
            -- we have h_dvd4 : p ∣ 2 + (p - 2) / g
            -- Since g ∣ p - 2 and g > 1:
            have hp_odd : p % 2 = 1 := by
              have : p % 2 ≠ 0 := by
                intro h_even
                have h_dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
                have hp_eq : p = 2 := (hp.eq_one_or_self_of_dvd 2 h_dvd |>.resolve_left (by omega)).symm
                omega
              omega
            have hq_odd : (p - 2) % 2 = 1 := by omega
            have hg_odd : g % 2 = 1 := by
              by_contra h_even
              have : g % 2 = 0 := by omega
              have : 2 ∣ g := Nat.dvd_of_mod_eq_zero this
              have : 2 ∣ p - 2 := dvd_trans this hg_dvd
              have : (p - 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
              omega
            have hg_ge3 : g ≥ 3 := by
              have : g ≥ 2 := by omega
              have : g ≠ 2 := by
                intro h_eq
                rw [h_eq] at hg_odd
                contradiction
              omega
            have h_div_le : (p - 2) / g ≤ (p - 2) / 3 := Nat.div_le_div_left hg_ge3 (by omega)
            have h_div_le2 : (p - 2) / 3 ≤ p / 3 := Nat.div_le_div_right (by omega)
            have h_div_lt : (p - 2) / g < p - 2 := by
              apply Nat.div_lt_self
              · omega
              · omega
            have h_sum_lt : 2 + (p - 2) / g < p := by
              clear h_div_le h_div_le2 h_dvd4
              omega
            have h_sum_pos : 2 + (p - 2) / g > 0 := by omega
            have : p ≤ 2 + (p - 2) / g := Nat.le_of_dvd h_sum_pos h_dvd4
            omega
      · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
        have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
        contradiction
