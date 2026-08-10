import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 500000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

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

lemma g_eq_one_of_not_dvd (N : ℕ) (hp : Nat.Prime N) (h_gt : N ≥ 1021)
  (h1 : ¬ N ∣ x_seq (N^2 - 3)) (h2 : N ∣ x_seq (N^2 - 2)) :
  Nat.gcd (x_seq (N^2 - 3)) (N^2 - 2) = 1 := by
  set g := Nat.gcd (x_seq (N^2 - 3)) (N^2 - 2)
  by_cases hg_eq1 : g = 1
  · exact hg_eq1
  · have h_N2 : N^2 ≥ 1042441 := by nlinarith
    have h_N2_pos : N^2 - 2 > 0 := by omega
    have hg_gt1 : g > 1 := by
      have : g > 0 := Nat.gcd_pos_of_pos_right _ h_N2_pos
      omega
    have h_recurrence := x_seq_step_eq_gen (N^2 - 2) (by omega)
    have h_eq_sub : N^2 - 2 - 1 = N^2 - 3 := by omega
    rw [h_eq_sub] at h_recurrence
    have h_dvd_sum : N ∣ 2 + (N^2 - 2) / g := by
      have h_mul : N ∣ x_seq (N^2 - 3) * (2 + (N^2 - 2)/g) := by
        rw [← h_recurrence]
        exact h2
      exact (Nat.Prime.dvd_mul hp).mp h_mul |>.resolve_left h1
    set m := (N^2 - 2) / g
    have h_dvd_sum_m : N ∣ 2 + m := h_dvd_sum
    have h_eq_g_m : g * m = N^2 - 2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rcases h_dvd_sum_m with ⟨k, hk⟩
    have h_eq_mul : g * (2 + m) = g * (N * k) := by rw [hk]
    have h_distrib : g * (2 + m) = 2 * g + g * m := by ring
    rw [h_distrib, h_eq_g_m] at h_eq_mul
    have h_eq_sub_2 : 2 * g - 2 = N * (g * k - N) := by
      have h_comm : g * (N * k) = N * (g * k) := by ring
      rw [h_comm] at h_eq_mul
      rw [Nat.mul_sub_left_distrib]
      have h_ring : N * N = N^2 := by ring
      rw [h_ring]
      omega
    have h_dvd_2_g_2 : N ∣ 2 * g - 2 := by
      rw [h_eq_sub_2]
      exact dvd_mul_right N (g * k - N)
    have hr_dvd_g_1 : N ∣ g - 1 := by
      have h_ring : 2 * g - 2 = 2 * (g - 1) := by omega
      rw [h_ring] at h_dvd_2_g_2
      have h_not_dvd_2 : ¬ N ∣ 2 := by
        intro h_dvd_2
        have : N ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
        omega
      exact (Nat.Prime.dvd_mul hp).mp h_dvd_2_g_2 |>.resolve_left h_not_dvd_2
    have hg_ge_N : g ≥ N + 1 := by
      rcases hr_dvd_g_1 with ⟨k2, hk2⟩
      have hk2_pos : k2 > 0 := by
        by_contra h_zero
        have : k2 = 0 := by omega
        rw [this] at hk2
        omega
      have : g - 1 ≥ N := by
        calc g - 1 = N * k2 := hk2
        _ ≥ N * 1 := Nat.mul_le_mul_left N hk2_pos
        _ = N := by ring
      omega
    have hg_dvd : g ∣ N^2 - 2 := Nat.gcd_dvd_right _ _
    have hk3_pos : (N^2 - 2) / g > 0 := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd h_N2_pos hg_dvd
      · omega
    set k3 := (N^2 - 2) / g
    have hk3_lt : k3 < N - 1 := by
      by_contra h_ge
      have h_le_mul : (N - 1) * (N + 1) ≤ k3 * g := Nat.mul_le_mul (by omega) hg_ge_N
      have h_ring : (N - 1) * (N + 1) = N^2 - 1 := by
        have h_N_pos : N > 0 := by omega
        generalize h_K : N - 1 = K
        have h_eq2 : N = K + 1 := by omega
        rw [h_eq2]
        have h_sq : (K + 1)^2 = K^2 + 2 * K + 1 := by ring
        rw [h_sq]
        have h_sub_1 : K^2 + 2 * K + 1 - 1 = K^2 + 2 * K := by omega
        rw [h_sub_1]
        have h_add : K + 1 + 1 = K + 2 := by omega
        rw [h_add]
        ring
      have h_comm : k3 * g = g * k3 := Nat.mul_comm _ _
      rw [h_comm, h_eq_g_m] at h_le_mul
      rw [h_ring] at h_le_mul
      omega
    have hk3_eq_N_2 : k3 = N - 2 := by
      have : N ∣ k3 + 2 := by
        rw [Nat.add_comm]
        exact h_dvd_sum
      rcases this with ⟨k4, hk4⟩
      have : k3 + 2 = N * k4 := hk4
      have : k4 = 1 := by
        by_contra h_ne
        have hk4_ne_zero : k4 ≠ 0 := by
          intro h_zero
          rw [h_zero, Nat.mul_zero] at hk4
          omega
        have : k4 ≥ 2 := by omega
        have : k3 + 2 ≥ N + N := by
          calc k3 + 2 = N * k4 := hk4
          _ ≥ N * 2 := Nat.mul_le_mul_left N this
          _ = N + N := by ring
        omega
      have : k3 + 2 = N := by
        rw [this, Nat.mul_one] at hk4
        exact hk4
      omega
    have hk3_dvd : k3 ∣ N^2 - 2 := by
      rw [← h_eq_g_m]
      exact dvd_mul_left k3 g
    rw [hk3_eq_N_2] at hk3_dvd
    have h_dvd_2 : N - 2 ∣ 2 := by
      have h_eq_ring : N^2 - 2 = (N - 2) * (N + 2) + 2 := by
        have h_ge : N ≥ 2 := by omega
        generalize h_K : N - 2 = K
        have h_eq2 : N = K + 2 := by omega
        rw [h_eq2]
        have h_sq : (K + 2)^2 = K^2 + 4 * K + 4 := by ring
        rw [h_sq]
        have h_sub_1 : K^2 + 4 * K + 4 - 2 = K^2 + 4 * K + 2 := by omega
        rw [h_sub_1]
        have h_add : K + 2 + 2 = K + 4 := by omega
        rw [h_add]
        ring
      rw [h_eq_ring] at hk3_dvd
      exact (Nat.dvd_add_iff_right (dvd_mul_right (N - 2) (N + 2))).mpr hk3_dvd
    have : N - 2 ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
    omega




