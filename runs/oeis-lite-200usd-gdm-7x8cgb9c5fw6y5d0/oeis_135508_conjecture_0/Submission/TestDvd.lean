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
lemma prime_dvd_x_seq_sq_sub_one_bounded_1039 (r : ℕ) (hr_le : r ≤ 1039) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := sorry

lemma sq_le_test (q r : ℕ) (h_q_lt : q < r) (hr : r ≥ 5) : q^2 - 1 ≤ r^2 - 3 := by
  have h_q_le : q ≤ r - 1 := by omega
  have h_q_sq : q * q ≤ (r - 1) * (r - 1) := Nat.mul_le_mul h_q_le h_q_le
  have h_q2 : q^2 = q * q := by ring
  have h_r1 : (r - 1)^2 = (r - 1) * (r - 1) := by ring
  rw [← h_q2, ← h_r1] at h_q_sq
  have h_r_eq : r = (r - 1) + 1 := by omega
  have h_id : r^2 + 1 = (r - 1)^2 + 2 * r := by
    conv =>
      lhs
      rw [h_r_eq]
    have h_rhs : (r - 1)^2 + 2 * r = (r - 1)^2 + 2 * ((r - 1) + 1) := by
      rw [← h_r_eq]
    rw [h_rhs]
    ring
  have h_ge_B : r^2 ≥ 2 * r := by
    have : r^2 = r * r := by ring
    rw [this]
    nlinarith
  generalize h_A : (r - 1)^2 = A at h_id h_q_sq
  generalize h_B : r^2 = B at h_id h_q_sq h_ge_B
  have h_ring : A = B - 2 * r + 1 := by omega
  rw [h_ring] at h_q_sq
  omega

lemma r_sub_2_sq_test (r : ℕ) (hr : r ≥ 5) : (r - 2)^2 - 1 ≤ r^2 - 5 := by
  have h_r_eq2 : r = (r - 2) + 2 := by omega
  have h_id2 : r^2 + 4 = (r - 2)^2 + 4 * r := by
    conv =>
      lhs
      rw [h_r_eq2]
    have h_rhs2 : (r - 2)^2 + 4 * r = (r - 2)^2 + 4 * ((r - 2) + 2) := by
      rw [← h_r_eq2]
    rw [h_rhs2]
    ring
  have h_ge_B2 : r^2 ≥ 4 * r := by
    have : r^2 = r * r := by ring
    rw [this]
    nlinarith
  generalize h_A2 : (r - 2)^2 = A2 at h_id2
  generalize h_B2 : r^2 = B2 at h_id2 h_ge_B2
  have h_ring2 : A2 - 1 ≤ B2 - 5 := by omega
  exact h_ring2

lemma r_sub_2_mul_test (r : ℕ) (hr : r ≥ 5) : (r - 2) * (r + 2) = r^2 - 4 := by
  have h_id_x (x : ℕ) : x * (x + 4) + 4 = (x + 2)^2 := by ring
  have h_val := h_id_x (r - 2)
  have h_sum_eq : r - 2 + 4 = r + 2 := by omega
  have h_r_eq2 : (r - 2) + 2 = r := by omega
  rw [h_sum_eq, h_r_eq2] at h_val
  have h_ring : (r - 2) * (r + 2) + 4 = r^2 := h_val
  omega

lemma g_eq_one_for_r (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 5)
  (h1 : ¬ r ∣ x_seq (r^2 - 3)) (h2 : r ∣ x_seq (r^2 - 2)) :
  Nat.gcd (x_seq (r^2 - 3)) (r^2 - 2) = 1 := by
  set g := Nat.gcd (x_seq (r^2 - 3)) (r^2 - 2)
  by_cases hg_eq1 : g = 1
  · exact hg_eq1
  · have hg_gt1 : g > 1 := by
      have h_pos : r^2 - 2 > 0 := by
        have : r^2 ≥ 25 := by
          have : r * r ≥ 5 * 5 := Nat.mul_le_mul hr_ge hr_ge
          have : r^2 = r * r := by ring
          omega
        omega
      have : g > 0 := Nat.gcd_pos_of_pos_right _ h_pos
      omega
    have hr_sq_ge : r^2 - 2 ≥ 2 := by
      have : r^2 ≥ 25 := by
        have : r * r ≥ 5 * 5 := Nat.mul_le_mul hr_ge hr_ge
        have : r^2 = r * r := by ring
        omega
      omega
    have h_recurrence := x_seq_step_eq_gen (r^2 - 2) hr_sq_ge
    have h_eq_sub : r^2 - 2 - 1 = r^2 - 3 := by omega
    rw [h_eq_sub] at h_recurrence
    have h_dvd_sum : r ∣ 2 + (r^2 - 2) / g := by
      have h_mul : r ∣ x_seq (r^2 - 3) * (2 + (r^2 - 2)/g) := by
        rw [← h_recurrence]
        exact h2
      exact (Nat.Prime.dvd_mul hr).mp h_mul |>.resolve_left h1
    set m := (r^2 - 2) / g
    have h_dvd_sum_m : r ∣ 2 + m := h_dvd_sum
    have h_eq_g_m : g * m = r^2 - 2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rcases h_dvd_sum_m with ⟨k, hk⟩
    have h_eq_mul : g * (2 + m) = g * (r * k) := by rw [hk]
    have h_distrib : g * (2 + m) = 2 * g + g * m := by ring
    rw [h_distrib, h_eq_g_m] at h_eq_mul
    have h_eq_sub_2 : 2 * g - 2 = r * (g * k - r) := by
      have h_dist : r * (g * k - r) = r * (g * k) - r * r := Nat.mul_sub_left_distrib r (g * k) r
      have h_r2 : r * r = r^2 := by ring
      rw [h_r2] at h_dist
      have h_assoc : r * (g * k) = r * g * k := by ring
      rw [h_assoc] at h_dist
      have h_comm : g * (r * k) = r * g * k := by ring
      have h_eq_mul' : 2 * g + (r^2 - 2) = r * g * k := by
        rw [← h_comm]
        exact h_eq_mul
      generalize h_B : r^2 = B at h_eq_mul' h_dist
      generalize h_C : r * g * k = C at h_eq_mul' h_dist
      omega
    have h_dvd_2_g_2 : r ∣ 2 * g - 2 := by
      rw [h_eq_sub_2]
      exact dvd_mul_right r (g * k - r)
    have hr_dvd_g_1 : r ∣ g - 1 := by
      have h_ring : 2 * g - 2 = 2 * (g - 1) := by omega
      rw [h_ring] at h_dvd_2_g_2
      have h_not_dvd_2 : ¬ r ∣ 2 := by
        intro h_dvd_2
        have : r ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
        omega
      exact (Nat.Prime.dvd_mul hr).mp h_dvd_2_g_2 |>.resolve_left h_not_dvd_2
    have hg_ge_r : g ≥ r + 1 := by
      rcases hr_dvd_g_1 with ⟨k2, hk2⟩
      have hk2_pos : k2 > 0 := by
        by_contra h_zero
        have : k2 = 0 := by omega
        rw [this] at hk2
        omega
      have : g - 1 ≥ r := by
        calc g - 1 = r * k2 := hk2
        _ ≥ r * 1 := Nat.mul_le_mul_left r hk2_pos
        _ = r := by ring
      omega
    have hm_ge : m ≥ r - 2 := by
      have hk_pos : k > 0 := by
        by_contra h_zero
        have : k = 0 := by omega
        rw [this] at hk
        simp at hk
      have : 2 + m ≥ r := by
        calc 2 + m = r * k := hk
        _ ≥ r * 1 := Nat.mul_le_mul_left r hk_pos
        _ = r := by ring
      omega
    by_cases h_cases : g - 1 = r
    · have hg_eq : g = r + 1 := by omega
      have h_dvd_g : g ∣ r^2 - 2 := Nat.gcd_dvd_right _ _
      rw [hg_eq] at h_dvd_g
      have h_id : (r + 1) * (r - 1) + 1 = r^2 := by
        have h_r_sub_add : r - 1 + 1 = r := by omega
        have h_r_eq3 : r + 1 = (r - 1) + 2 := by omega
        have h_sq : r^2 = (r - 1 + 1) * (r - 1 + 1) := by
          rw [h_r_sub_add]
          ring
        rw [h_r_eq3, h_sq]
        ring
      have h_id_sub : (r + 1) * (r - 1) = r^2 - 1 := by omega
      have h_dvd_id : r + 1 ∣ (r + 1) * (r - 1) := dvd_mul_right (r + 1) (r - 1)
      rw [h_id_sub] at h_dvd_id
      have h_sub_dvd : r + 1 ∣ (r^2 - 1) - (r^2 - 2) := Nat.dvd_sub h_dvd_id h_dvd_g
      have : (r^2 - 1) - (r^2 - 2) = 1 := by omega
      rw [this] at h_sub_dvd
      have : r + 1 = 1 := Nat.eq_one_of_dvd_one h_sub_dvd
      omega
    · have hg_ge_2r : g - 1 ≥ 2 * r := by
        rcases hr_dvd_g_1 with ⟨k4, hk4⟩
        have hk4_pos : k4 > 0 := by
          by_contra h_zero
          have : k4 = 0 := by omega
          rw [this] at hk4
          omega
        have hk4_ge_2 : k4 ≥ 2 := by
          by_contra h_lt
          have : k4 = 1 := by omega
          rw [this] at hk4
          have : g - 1 = r := by omega
          contradiction
        calc g - 1 = r * k4 := hk4
        _ ≥ r * 2 := Nat.mul_le_mul_left r hk4_ge_2
        _ = 2 * r := by ring
      have hg_ge2 : g ≥ 2 * r + 1 := by omega
      have h_prod_ge : g * m ≥ (2 * r + 1) * (r - 2) := Nat.mul_le_mul hg_ge2 hm_ge
      have h_id_x (x : ℕ) : (2 * (x + 2) + 1) * x + 3 * (x + 2) + 2 = 2 * (x + 2)^2 := by ring
      have h_id4 := h_id_x (r - 2)
      have h_r_eq2 : (r - 2) + 2 = r := by omega
      rw [h_r_eq2] at h_id4
      have h_id5 : (2 * r + 1) * (r - 2) = 2 * r^2 - 3 * r - 2 := by omega
      rw [h_id5] at h_prod_ge
      have h_r_sq_gt : r^2 > 3 * r := by
        have : r^2 = r * r := by ring
        rw [this]
        have : r * r ≥ 5 * r := Nat.mul_le_mul_right r hr_ge
        omega
      have : 2 * r^2 - 3 * r - 2 > r^2 - 2 := by omega
      omega

lemma prime_dvd_x_seq_sq_sub_one (r : ℕ) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  induction' r using Nat.strong_induction_on with r ih
  by_cases h_le : r ≤ 1039
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1039 r h_le hr
  · have hr_ge : r ≥ 5 := by omega
    have h_r2_sub_2_pos : r^2 - 2 > 0 := by
      have : r^2 ≥ 25 := by
        have : r * r ≥ 5 * 5 := Nat.mul_le_mul hr_ge hr_ge
        have : r^2 = r * r := by ring
        omega
      omega
    have h_dvd : x_seq (r^2 - 2) ∣ x_seq (r^2 - 1) := by
      apply x_seq_dvd_of_le
      · exact h_r2_sub_2_pos
      · omega
    apply dvd_trans _ h_dvd
    set n := r^2 - 2
    have hn : n ≥ 2 := by
      have : r^2 ≥ 25 := by
        have : r * r ≥ 5 * 5 := Nat.mul_le_mul hr_ge hr_ge
        have : r^2 = r * r := by ring
        omega
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
    · have h_dvd2 : x_seq (n - 1) ∣ x_seq n := by
        have h_pos : n - 1 > 0 := by omega
        have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        rw [← h_eq]
        exact x_seq_dvd (n - 1) h_pos
      -- Wait, if r ∣/ x_seq (n-1), we want to prove r ∣ x_seq n.
      -- x_seq n = x_seq (n - 1) * (2 + k).
      -- So if r ∣ 2 + k, then r ∣ x_seq n.
      have h_g_eq : g = 1 := by
        -- wait!
        -- since r is prime, and r ∣/ x_seq (n-1) (which is r ∣/ x_seq (r^2 - 3)),
        -- wait, if we also had r ∣ x_seq n (which is h2), then we would call g_eq_one_for_r!
        -- but wait! We don't have r ∣ x_seq n yet!
        -- Ah!
        sorry









