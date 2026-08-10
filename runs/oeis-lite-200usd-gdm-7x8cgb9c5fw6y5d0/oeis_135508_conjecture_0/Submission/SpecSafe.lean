import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 20000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

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

lemma A135508_eq (p : ℕ) (hp : Nat.Prime p) : A135508 (p - 1) = (x_seq p / x_seq (p - 1)) - 2 := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hp_sub_1_ne_zero : p - 1 ≠ 0 := by omega
  have h_cancel : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  unfold A135508
  split_ifs
  · contradiction
  · dsimp only
    rw [h_cancel]

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

lemma x_seq_div_eq (p : ℕ) (hp : Nat.Prime p) : x_seq p / x_seq (p - 1) = 2 + p / Nat.gcd (x_seq (p - 1)) p := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_cancel : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have h_pos : x_seq (p - 1) > 0 := by
    apply x_seq_pos
    omega
  have h_x_seq_p : x_seq p = 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) p := by
    have h_step : x_seq (p - 1 + 1) = 2 * x_seq (p - 1) + Nat.lcm (x_seq (p - 1)) (p - 1 + 1) := by
      rw [x_seq]
      omega
    rw [h_cancel] at h_step
    exact h_step
  rw [h_x_seq_p]
  have h_comm_mul : 2 * x_seq (p - 1) = x_seq (p - 1) * 2 := Nat.mul_comm _ _
  rw [h_comm_mul]
  rw [div_add_rule (x_seq (p - 1)) 2 (Nat.lcm (x_seq (p - 1)) p) h_pos]
  rw [lcm_div_rule (x_seq (p - 1)) p h_pos]

lemma A135508_p_eq (p : ℕ) (hp : Nat.Prime p) : A135508 (p - 1) = p / Nat.gcd (x_seq (p - 1)) p := by
  rw [A135508_eq p hp, x_seq_div_eq p hp]
  have h_comm : 2 + p / Nat.gcd (x_seq (p - 1)) p = p / Nat.gcd (x_seq (p - 1)) p + 2 := Nat.add_comm _ _
  rw [h_comm]
  exact Nat.add_sub_cancel _ _

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

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | i + 1, idx, acc => x_seq_loop i (idx + 1) (2 * acc + Nat.lcm acc idx)

def x_seq_tail (n : ℕ) : ℕ :=
  if n = 0 then 0 else x_seq_loop (n - 1) 2 1

lemma x_seq_step (idx : ℕ) (hidx : idx ≥ 2) : x_seq idx = 2 * x_seq (idx - 1) + Nat.lcm (x_seq (idx - 1)) idx := by
  have h_eq : idx = idx - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
  nth_rw 1 [h_eq]
  rw [x_seq]
  · have h_eq2 : idx - 1 + 1 = idx := Nat.sub_add_cancel (by omega)
    rw [h_eq2]
  · omega

lemma x_seq_loop_lemma (i : ℕ) :
  ∀ idx acc, idx ≥ 2 → acc = x_seq (idx - 1) → x_seq_loop i idx acc = x_seq (i + idx - 1) := by
  induction i with
  | zero =>
    intro idx acc hidx hacc
    simp [x_seq_loop, hacc]
  | succ k ih =>
    intro idx acc hidx hacc
    simp [x_seq_loop]
    have h_acc' : 2 * acc + Nat.lcm acc idx = x_seq idx := by
      rw [hacc]
      exact (x_seq_step idx hidx).symm
    have h_idx' : idx + 1 ≥ 2 := by omega
    have h_acc_eq : 2 * acc + Nat.lcm acc idx = x_seq (idx + 1 - 1) := by
      rw [h_acc']
      have : idx + 1 - 1 = idx := by omega
      rw [this]
    have h_ih := ih (idx + 1) (2 * acc + Nat.lcm acc idx) h_idx' h_acc_eq
    rw [h_ih]
    congr 1

lemma x_seq_eq_x_seq_tail (n : ℕ) : x_seq n = x_seq_tail n := by
  by_cases hn : n = 0
  · simp [hn, x_seq_tail]
    rfl
  · simp [x_seq_tail, hn]
    have h_loop := x_seq_loop_lemma (n - 1) 2 1 (by omega) (by rfl)
    rw [h_loop]
    congr 1; omega

lemma prime_not_dvd_x_seq_small (p : ℕ) (hp_lt : p < 600) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  revert hp hp2 hp_lt p
  decide

lemma prime_dvd_x_seq_sq_sub_one_bounded (r : ℕ) (hr_lt : r < 15) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  revert hr hr_lt r
  decide
lemma dvd_17_aux : 17 ∣ x_seq 83 := by
      rw [x_seq_eq_x_seq_tail 83]
      decide
lemma dvd_17 : 17 ∣ x_seq (17^2 - 1) := by
  have h_dvd : x_seq 83 ∣ x_seq (17^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_17_aux h_dvd

lemma dvd_19_aux : 19 ∣ x_seq 17 := by
      rw [x_seq_eq_x_seq_tail 17]
      decide
lemma dvd_19 : 19 ∣ x_seq (19^2 - 1) := by
  have h_dvd : x_seq 17 ∣ x_seq (19^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_19_aux h_dvd

lemma dvd_23_aux : 23 ∣ x_seq 67 := by
      rw [x_seq_eq_x_seq_tail 67]
      decide
lemma dvd_23 : 23 ∣ x_seq (23^2 - 1) := by
  have h_dvd : x_seq 67 ∣ x_seq (23^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_23_aux h_dvd

lemma dvd_29_aux : 29 ∣ x_seq 317 := by
      rw [x_seq_eq_x_seq_tail 317]
      decide
lemma dvd_29 : 29 ∣ x_seq (29^2 - 1) := by
  have h_dvd : x_seq 317 ∣ x_seq (29^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_29_aux h_dvd

lemma dvd_31_aux : 31 ∣ x_seq 29 := by
      rw [x_seq_eq_x_seq_tail 29]
      decide
lemma dvd_31 : 31 ∣ x_seq (31^2 - 1) := by
  have h_dvd : x_seq 29 ∣ x_seq (31^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_31_aux h_dvd

lemma dvd_37_aux : 37 ∣ x_seq 257 := by
      rw [x_seq_eq_x_seq_tail 257]
      decide
lemma dvd_37 : 37 ∣ x_seq (37^2 - 1) := by
  have h_dvd : x_seq 257 ∣ x_seq (37^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_37_aux h_dvd

lemma dvd_41_aux : 41 ∣ x_seq 367 := by
      rw [x_seq_eq_x_seq_tail 367]
      decide
lemma dvd_41 : 41 ∣ x_seq (41^2 - 1) := by
  have h_dvd : x_seq 367 ∣ x_seq (41^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_41_aux h_dvd

lemma dvd_43_aux : 43 ∣ x_seq 41 := by
      rw [x_seq_eq_x_seq_tail 41]
      decide
lemma dvd_43 : 43 ∣ x_seq (43^2 - 1) := by
  have h_dvd : x_seq 41 ∣ x_seq (43^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_43_aux h_dvd

lemma dvd_47_aux : 47 ∣ x_seq 233 := by
      rw [x_seq_eq_x_seq_tail 233]
      decide
lemma dvd_47 : 47 ∣ x_seq (47^2 - 1) := by
  have h_dvd : x_seq 233 ∣ x_seq (47^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_47_aux h_dvd

lemma dvd_53_aux : 53 ∣ x_seq 157 := by
      rw [x_seq_eq_x_seq_tail 157]
      decide
lemma dvd_53 : 53 ∣ x_seq (53^2 - 1) := by
  have h_dvd : x_seq 157 ∣ x_seq (53^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_53_aux h_dvd

lemma dvd_59_aux : 59 ∣ x_seq 293 := by
      rw [x_seq_eq_x_seq_tail 293]
      decide
lemma dvd_59 : 59 ∣ x_seq (59^2 - 1) := by
  have h_dvd : x_seq 293 ∣ x_seq (59^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_59_aux h_dvd

lemma dvd_61_aux : 61 ∣ x_seq 59 := by
      rw [x_seq_eq_x_seq_tail 59]
      decide
lemma dvd_61 : 61 ∣ x_seq (61^2 - 1) := by
  have h_dvd : x_seq 59 ∣ x_seq (61^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_61_aux h_dvd

lemma dvd_67_aux : 67 ∣ x_seq 467 := by
      rw [x_seq_eq_x_seq_tail 467]
      decide
lemma dvd_67 : 67 ∣ x_seq (67^2 - 1) := by
  have h_dvd : x_seq 467 ∣ x_seq (67^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_67_aux h_dvd

lemma dvd_71_aux : 71 ∣ x_seq 211 := by
      rw [x_seq_eq_x_seq_tail 211]
      decide
lemma dvd_71 : 71 ∣ x_seq (71^2 - 1) := by
  have h_dvd : x_seq 211 ∣ x_seq (71^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_71_aux h_dvd

lemma dvd_73_aux : 73 ∣ x_seq 71 := by
      rw [x_seq_eq_x_seq_tail 71]
      decide
lemma dvd_73 : 73 ∣ x_seq (73^2 - 1) := by
  have h_dvd : x_seq 71 ∣ x_seq (73^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_73_aux h_dvd

lemma dvd_79_aux : 79 ∣ x_seq 709 := by
      rw [x_seq_eq_x_seq_tail 709]
      decide
lemma dvd_79 : 79 ∣ x_seq (79^2 - 1) := by
  have h_dvd : x_seq 709 ∣ x_seq (79^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_79_aux h_dvd

lemma dvd_83_aux : 83 ∣ x_seq 911 := by
      rw [x_seq_eq_x_seq_tail 911]
      decide
lemma dvd_83 : 83 ∣ x_seq (83^2 - 1) := by
  have h_dvd : x_seq 911 ∣ x_seq (83^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_83_aux h_dvd

lemma dvd_89_aux : 89 ∣ x_seq 443 := by
      rw [x_seq_eq_x_seq_tail 443]
      decide
lemma dvd_89 : 89 ∣ x_seq (89^2 - 1) := by
  have h_dvd : x_seq 443 ∣ x_seq (89^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_89_aux h_dvd

lemma dvd_97_aux : 97 ∣ x_seq 677 := by
      rw [x_seq_eq_x_seq_tail 677]
      decide
lemma dvd_97 : 97 ∣ x_seq (97^2 - 1) := by
  have h_dvd : x_seq 677 ∣ x_seq (97^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_97_aux h_dvd

lemma dvd_101_aux : 101 ∣ x_seq 503 := by
      rw [x_seq_eq_x_seq_tail 503]
      decide
lemma dvd_101 : 101 ∣ x_seq (101^2 - 1) := by
  have h_dvd : x_seq 503 ∣ x_seq (101^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_101_aux h_dvd

lemma dvd_103_aux : 103 ∣ x_seq 101 := by
      rw [x_seq_eq_x_seq_tail 101]
      decide
lemma dvd_103 : 103 ∣ x_seq (103^2 - 1) := by
  have h_dvd : x_seq 101 ∣ x_seq (103^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_103_aux h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_103 (r : ℕ) (hr_le : r ≤ 103) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r < 15
  · exact prime_dvd_x_seq_sq_sub_one_bounded r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 15) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 16) hr |>.elim
    · exact dvd_17
    · exact (by decide : ¬ Nat.Prime 18) hr |>.elim
    · exact dvd_19
    · exact (by decide : ¬ Nat.Prime 20) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 21) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 22) hr |>.elim
    · exact dvd_23
    · exact (by decide : ¬ Nat.Prime 24) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 25) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 26) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 27) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 28) hr |>.elim
    · exact dvd_29
    · exact (by decide : ¬ Nat.Prime 30) hr |>.elim
    · exact dvd_31
    · exact (by decide : ¬ Nat.Prime 32) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 33) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 34) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 35) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 36) hr |>.elim
    · exact dvd_37
    · exact (by decide : ¬ Nat.Prime 38) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 39) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 40) hr |>.elim
    · exact dvd_41
    · exact (by decide : ¬ Nat.Prime 42) hr |>.elim
    · exact dvd_43
    · exact (by decide : ¬ Nat.Prime 44) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 45) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 46) hr |>.elim
    · exact dvd_47
    · exact (by decide : ¬ Nat.Prime 48) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 49) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 50) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 51) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 52) hr |>.elim
    · exact dvd_53
    · exact (by decide : ¬ Nat.Prime 54) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 55) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 56) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 57) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 58) hr |>.elim
    · exact dvd_59
    · exact (by decide : ¬ Nat.Prime 60) hr |>.elim
    · exact dvd_61
    · exact (by decide : ¬ Nat.Prime 62) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 63) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 64) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 65) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 66) hr |>.elim
    · exact dvd_67
    · exact (by decide : ¬ Nat.Prime 68) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 69) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 70) hr |>.elim
    · exact dvd_71
    · exact (by decide : ¬ Nat.Prime 72) hr |>.elim
    · exact dvd_73
    · exact (by decide : ¬ Nat.Prime 74) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 75) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 76) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 77) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 78) hr |>.elim
    · exact dvd_79
    · exact (by decide : ¬ Nat.Prime 80) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 81) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 82) hr |>.elim
    · exact dvd_83
    · exact (by decide : ¬ Nat.Prime 84) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 85) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 86) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 87) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 88) hr |>.elim
    · exact dvd_89
    · exact (by decide : ¬ Nat.Prime 90) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 91) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 92) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 93) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 94) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 95) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 96) hr |>.elim
    · exact dvd_97
    · exact (by decide : ¬ Nat.Prime 98) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 99) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 100) hr |>.elim
    · exact dvd_101
    · exact (by decide : ¬ Nat.Prime 102) hr |>.elim
    · exact dvd_103

lemma prime_not_dvd_x_seq_103 (p : ℕ) (hp_lt : p < 11451) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  by_cases hp_lt_600 : p < 600
  · exact prime_not_dvd_x_seq_small p hp_lt_600 hp hp2
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
          have hg_pos : g > 0 := Nat.gcd_pos_of_pos_right _ hq_pos
          have hg_cases : g = 1 ∨ g > 1 := by omega
          rcases hg_cases with hg_eq1 | hg_gt1
          · clear h_dvd4
            have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
            set r := Nat.minFac (p - 2)
            have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
            have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
            have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
            have hr_le : r ≤ 103 := by
              by_contra h_gt
              have hr_ge_104 : r ≥ 104 := by omega
              have hr_ge_107 : r ≥ 107 := by
                by_contra h_lt
                have : r = 104 ∨ r = 105 ∨ r = 106 := by omega
                rcases this with h_r | h_r | h_r
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 104) hr_prime |>.elim
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 105) hr_prime |>.elim
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 106) hr_prime |>.elim
              have : r^2 ≥ 11449 := by nlinarith
              have : p - 2 < 11449 := by omega
              omega
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_103 r hr_le hr_prime
            have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
            have h_r2_sub_1_pos : r^2 - 1 > 0 := by
              have : r ≥ 2 := Nat.Prime.two_le hr_prime
              have : r^2 ≥ 4 := by nlinarith
              omega
            have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
            have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
            have h_r_dvd_gcd : r ∣ g := Nat.dvd_gcd h_r_dvd_x hr_dvd
            rw [hg_eq1] at h_r_dvd_gcd
            have : r ∣ 1 := h_r_dvd_gcd
            have : r = 1 := Nat.eq_one_of_dvd_one this
            have : r ≥ 2 := Nat.Prime.two_le hr_prime
            omega
          · have hp_odd : p % 2 = 1 := by
              have : p % 2 ≠ 0 := by
                intro h_even
                have h_dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
                have hp_eq : p = 2 := (hp.eq_one_or_self_of_dvd 2 h_dvd |>.resolve_left (by omega)).symm
                omega
              omega
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
            have h_div_lt : (p - 2) / g < p - 2 := by
              apply Nat.div_lt_self
              · omega
              · omega
            have h_sum_lt : 2 + (p - 2) / g < p := by
              clear hp_odd hg_odd hg_ge3 hg_dvd h_dvd4
              omega
            have h_sum_pos : 2 + (p - 2) / g > 0 := by
              have : (p - 2) / g ≥ 0 := Nat.zero_le _
              omega
            have : p ≤ 2 + (p - 2) / g := Nat.le_of_dvd h_sum_pos h_dvd4
            omega
      · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
        have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
        contradiction
attribute [irreducible] x_seq

lemma dvd_107_aux : 107 ∣ x_seq 2459 := by
  have h_step : x_seq 2459 = x_seq (2459 - 1) * (2 + 2459 / Nat.gcd (x_seq (2459 - 1)) 2459) := by
    exact x_seq_step_eq_gen 2459 (by decide)
  have h_gcd : Nat.gcd (x_seq (2459 - 1)) 2459 = 1 := prime_not_dvd_x_seq_103 2459 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 2459 / 1 = 2459 := Nat.div_one 2459
  rw [h_div] at h_step
  have h_add : 2 + 2459 = 2461 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 107 ∣ 2461 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_107 : 107 ∣ x_seq (107^2 - 1) := by
  have h_dvd : x_seq 2459 ∣ x_seq (107^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_107_aux h_dvd
lemma dvd_109_aux : 109 ∣ x_seq 107 := by
  have h_step : x_seq 107 = x_seq (107 - 1) * (2 + 107 / Nat.gcd (x_seq (107 - 1)) 107) := by
    exact x_seq_step_eq_gen 107 (by decide)
  have h_gcd : Nat.gcd (x_seq (107 - 1)) 107 = 1 := prime_not_dvd_x_seq_103 107 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 107 / 1 = 107 := Nat.div_one 107
  rw [h_div] at h_step
  have h_add : 2 + 107 = 109 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 109 ∣ 109 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_109 : 109 ∣ x_seq (109^2 - 1) := by
  have h_dvd : x_seq 107 ∣ x_seq (109^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_109_aux h_dvd
lemma dvd_113_aux : 113 ∣ x_seq 337 := by
  have h_step : x_seq 337 = x_seq (337 - 1) * (2 + 337 / Nat.gcd (x_seq (337 - 1)) 337) := by
    exact x_seq_step_eq_gen 337 (by decide)
  have h_gcd : Nat.gcd (x_seq (337 - 1)) 337 = 1 := prime_not_dvd_x_seq_103 337 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 337 / 1 = 337 := Nat.div_one 337
  rw [h_div] at h_step
  have h_add : 2 + 337 = 339 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 113 ∣ 339 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_113 : 113 ∣ x_seq (113^2 - 1) := by
  have h_dvd : x_seq 337 ∣ x_seq (113^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_113_aux h_dvd
lemma dvd_127_aux : 127 ∣ x_seq 379 := by
  have h_step : x_seq 379 = x_seq (379 - 1) * (2 + 379 / Nat.gcd (x_seq (379 - 1)) 379) := by
    exact x_seq_step_eq_gen 379 (by decide)
  have h_gcd : Nat.gcd (x_seq (379 - 1)) 379 = 1 := prime_not_dvd_x_seq_103 379 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 379 / 1 = 379 := Nat.div_one 379
  rw [h_div] at h_step
  have h_add : 2 + 379 = 381 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 127 ∣ 381 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_127 : 127 ∣ x_seq (127^2 - 1) := by
  have h_dvd : x_seq 379 ∣ x_seq (127^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_127_aux h_dvd
lemma dvd_131_aux : 131 ∣ x_seq 653 := by
  have h_step : x_seq 653 = x_seq (653 - 1) * (2 + 653 / Nat.gcd (x_seq (653 - 1)) 653) := by
    exact x_seq_step_eq_gen 653 (by decide)
  have h_gcd : Nat.gcd (x_seq (653 - 1)) 653 = 1 := prime_not_dvd_x_seq_103 653 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 653 / 1 = 653 := Nat.div_one 653
  rw [h_div] at h_step
  have h_add : 2 + 653 = 655 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 131 ∣ 655 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_131 : 131 ∣ x_seq (131^2 - 1) := by
  have h_dvd : x_seq 653 ∣ x_seq (131^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_131_aux h_dvd
lemma dvd_137_aux : 137 ∣ x_seq 409 := by
  have h_step : x_seq 409 = x_seq (409 - 1) * (2 + 409 / Nat.gcd (x_seq (409 - 1)) 409) := by
    exact x_seq_step_eq_gen 409 (by decide)
  have h_gcd : Nat.gcd (x_seq (409 - 1)) 409 = 1 := prime_not_dvd_x_seq_103 409 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 409 / 1 = 409 := Nat.div_one 409
  rw [h_div] at h_step
  have h_add : 2 + 409 = 411 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 137 ∣ 411 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_137 : 137 ∣ x_seq (137^2 - 1) := by
  have h_dvd : x_seq 409 ∣ x_seq (137^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_137_aux h_dvd
lemma dvd_139_aux : 139 ∣ x_seq 137 := by
  have h_step : x_seq 137 = x_seq (137 - 1) * (2 + 137 / Nat.gcd (x_seq (137 - 1)) 137) := by
    exact x_seq_step_eq_gen 137 (by decide)
  have h_gcd : Nat.gcd (x_seq (137 - 1)) 137 = 1 := prime_not_dvd_x_seq_103 137 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 137 / 1 = 137 := Nat.div_one 137
  rw [h_div] at h_step
  have h_add : 2 + 137 = 139 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 139 ∣ 139 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_139 : 139 ∣ x_seq (139^2 - 1) := by
  have h_dvd : x_seq 137 ∣ x_seq (139^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_139_aux h_dvd
lemma dvd_149_aux : 149 ∣ x_seq 743 := by
  have h_step : x_seq 743 = x_seq (743 - 1) * (2 + 743 / Nat.gcd (x_seq (743 - 1)) 743) := by
    exact x_seq_step_eq_gen 743 (by decide)
  have h_gcd : Nat.gcd (x_seq (743 - 1)) 743 = 1 := prime_not_dvd_x_seq_103 743 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 743 / 1 = 743 := Nat.div_one 743
  rw [h_div] at h_step
  have h_add : 2 + 743 = 745 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 149 ∣ 745 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_149 : 149 ∣ x_seq (149^2 - 1) := by
  have h_dvd : x_seq 743 ∣ x_seq (149^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_149_aux h_dvd
lemma dvd_151_aux : 151 ∣ x_seq 149 := by
  have h_step : x_seq 149 = x_seq (149 - 1) * (2 + 149 / Nat.gcd (x_seq (149 - 1)) 149) := by
    exact x_seq_step_eq_gen 149 (by decide)
  have h_gcd : Nat.gcd (x_seq (149 - 1)) 149 = 1 := prime_not_dvd_x_seq_103 149 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 149 / 1 = 149 := Nat.div_one 149
  rw [h_div] at h_step
  have h_add : 2 + 149 = 151 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 151 ∣ 151 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_151 : 151 ∣ x_seq (151^2 - 1) := by
  have h_dvd : x_seq 149 ∣ x_seq (151^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_151_aux h_dvd
lemma dvd_157_aux : 157 ∣ x_seq 1097 := by
  have h_step : x_seq 1097 = x_seq (1097 - 1) * (2 + 1097 / Nat.gcd (x_seq (1097 - 1)) 1097) := by
    exact x_seq_step_eq_gen 1097 (by decide)
  have h_gcd : Nat.gcd (x_seq (1097 - 1)) 1097 = 1 := prime_not_dvd_x_seq_103 1097 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1097 / 1 = 1097 := Nat.div_one 1097
  rw [h_div] at h_step
  have h_add : 2 + 1097 = 1099 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 157 ∣ 1099 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_157 : 157 ∣ x_seq (157^2 - 1) := by
  have h_dvd : x_seq 1097 ∣ x_seq (157^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_157_aux h_dvd
lemma dvd_163_aux : 163 ∣ x_seq 487 := by
  have h_step : x_seq 487 = x_seq (487 - 1) * (2 + 487 / Nat.gcd (x_seq (487 - 1)) 487) := by
    exact x_seq_step_eq_gen 487 (by decide)
  have h_gcd : Nat.gcd (x_seq (487 - 1)) 487 = 1 := prime_not_dvd_x_seq_103 487 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 487 / 1 = 487 := Nat.div_one 487
  rw [h_div] at h_step
  have h_add : 2 + 487 = 489 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 163 ∣ 489 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_163 : 163 ∣ x_seq (163^2 - 1) := by
  have h_dvd : x_seq 487 ∣ x_seq (163^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_163_aux h_dvd
lemma dvd_167_aux : 167 ∣ x_seq 499 := by
  have h_step : x_seq 499 = x_seq (499 - 1) * (2 + 499 / Nat.gcd (x_seq (499 - 1)) 499) := by
    exact x_seq_step_eq_gen 499 (by decide)
  have h_gcd : Nat.gcd (x_seq (499 - 1)) 499 = 1 := prime_not_dvd_x_seq_103 499 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 499 / 1 = 499 := Nat.div_one 499
  rw [h_div] at h_step
  have h_add : 2 + 499 = 501 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 167 ∣ 501 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_167 : 167 ∣ x_seq (167^2 - 1) := by
  have h_dvd : x_seq 499 ∣ x_seq (167^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_167_aux h_dvd
lemma dvd_173_aux : 173 ∣ x_seq 863 := by
  have h_step : x_seq 863 = x_seq (863 - 1) * (2 + 863 / Nat.gcd (x_seq (863 - 1)) 863) := by
    exact x_seq_step_eq_gen 863 (by decide)
  have h_gcd : Nat.gcd (x_seq (863 - 1)) 863 = 1 := prime_not_dvd_x_seq_103 863 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 863 / 1 = 863 := Nat.div_one 863
  rw [h_div] at h_step
  have h_add : 2 + 863 = 865 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 173 ∣ 865 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_173 : 173 ∣ x_seq (173^2 - 1) := by
  have h_dvd : x_seq 863 ∣ x_seq (173^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_173_aux h_dvd
lemma dvd_179_aux : 179 ∣ x_seq 2683 := by
  have h_step : x_seq 2683 = x_seq (2683 - 1) * (2 + 2683 / Nat.gcd (x_seq (2683 - 1)) 2683) := by
    exact x_seq_step_eq_gen 2683 (by decide)
  have h_gcd : Nat.gcd (x_seq (2683 - 1)) 2683 = 1 := prime_not_dvd_x_seq_103 2683 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 2683 / 1 = 2683 := Nat.div_one 2683
  rw [h_div] at h_step
  have h_add : 2 + 2683 = 2685 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 179 ∣ 2685 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_179 : 179 ∣ x_seq (179^2 - 1) := by
  have h_dvd : x_seq 2683 ∣ x_seq (179^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_179_aux h_dvd
lemma dvd_181_aux : 181 ∣ x_seq 179 := by
  have h_step : x_seq 179 = x_seq (179 - 1) * (2 + 179 / Nat.gcd (x_seq (179 - 1)) 179) := by
    exact x_seq_step_eq_gen 179 (by decide)
  have h_gcd : Nat.gcd (x_seq (179 - 1)) 179 = 1 := prime_not_dvd_x_seq_103 179 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 179 / 1 = 179 := Nat.div_one 179
  rw [h_div] at h_step
  have h_add : 2 + 179 = 181 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 181 ∣ 181 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_181 : 181 ∣ x_seq (181^2 - 1) := by
  have h_dvd : x_seq 179 ∣ x_seq (181^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_181_aux h_dvd
lemma dvd_191_aux : 191 ∣ x_seq 953 := by
  have h_step : x_seq 953 = x_seq (953 - 1) * (2 + 953 / Nat.gcd (x_seq (953 - 1)) 953) := by
    exact x_seq_step_eq_gen 953 (by decide)
  have h_gcd : Nat.gcd (x_seq (953 - 1)) 953 = 1 := prime_not_dvd_x_seq_103 953 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 953 / 1 = 953 := Nat.div_one 953
  rw [h_div] at h_step
  have h_add : 2 + 953 = 955 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 191 ∣ 955 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_191 : 191 ∣ x_seq (191^2 - 1) := by
  have h_dvd : x_seq 953 ∣ x_seq (191^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_191_aux h_dvd
lemma dvd_193_aux : 193 ∣ x_seq 191 := by
  have h_step : x_seq 191 = x_seq (191 - 1) * (2 + 191 / Nat.gcd (x_seq (191 - 1)) 191) := by
    exact x_seq_step_eq_gen 191 (by decide)
  have h_gcd : Nat.gcd (x_seq (191 - 1)) 191 = 1 := prime_not_dvd_x_seq_103 191 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 191 / 1 = 191 := Nat.div_one 191
  rw [h_div] at h_step
  have h_add : 2 + 191 = 193 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 193 ∣ 193 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_193 : 193 ∣ x_seq (193^2 - 1) := by
  have h_dvd : x_seq 191 ∣ x_seq (193^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_193_aux h_dvd
lemma dvd_197_aux : 197 ∣ x_seq 983 := by
  have h_step : x_seq 983 = x_seq (983 - 1) * (2 + 983 / Nat.gcd (x_seq (983 - 1)) 983) := by
    exact x_seq_step_eq_gen 983 (by decide)
  have h_gcd : Nat.gcd (x_seq (983 - 1)) 983 = 1 := prime_not_dvd_x_seq_103 983 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 983 / 1 = 983 := Nat.div_one 983
  rw [h_div] at h_step
  have h_add : 2 + 983 = 985 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 197 ∣ 985 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_197 : 197 ∣ x_seq (197^2 - 1) := by
  have h_dvd : x_seq 983 ∣ x_seq (197^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_197_aux h_dvd
lemma dvd_199_aux : 199 ∣ x_seq 197 := by
  have h_step : x_seq 197 = x_seq (197 - 1) * (2 + 197 / Nat.gcd (x_seq (197 - 1)) 197) := by
    exact x_seq_step_eq_gen 197 (by decide)
  have h_gcd : Nat.gcd (x_seq (197 - 1)) 197 = 1 := prime_not_dvd_x_seq_103 197 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 197 / 1 = 197 := Nat.div_one 197
  rw [h_div] at h_step
  have h_add : 2 + 197 = 199 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 199 ∣ 199 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_199 : 199 ∣ x_seq (199^2 - 1) := by
  have h_dvd : x_seq 197 ∣ x_seq (199^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_199_aux h_dvd
lemma dvd_211_aux : 211 ∣ x_seq 631 := by
  have h_step : x_seq 631 = x_seq (631 - 1) * (2 + 631 / Nat.gcd (x_seq (631 - 1)) 631) := by
    exact x_seq_step_eq_gen 631 (by decide)
  have h_gcd : Nat.gcd (x_seq (631 - 1)) 631 = 1 := prime_not_dvd_x_seq_103 631 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 631 / 1 = 631 := Nat.div_one 631
  rw [h_div] at h_step
  have h_add : 2 + 631 = 633 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 211 ∣ 633 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_211 : 211 ∣ x_seq (211^2 - 1) := by
  have h_dvd : x_seq 631 ∣ x_seq (211^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_211_aux h_dvd
lemma dvd_223_aux : 223 ∣ x_seq 1559 := by
  have h_step : x_seq 1559 = x_seq (1559 - 1) * (2 + 1559 / Nat.gcd (x_seq (1559 - 1)) 1559) := by
    exact x_seq_step_eq_gen 1559 (by decide)
  have h_gcd : Nat.gcd (x_seq (1559 - 1)) 1559 = 1 := prime_not_dvd_x_seq_103 1559 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1559 / 1 = 1559 := Nat.div_one 1559
  rw [h_div] at h_step
  have h_add : 2 + 1559 = 1561 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 223 ∣ 1561 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_223 : 223 ∣ x_seq (223^2 - 1) := by
  have h_dvd : x_seq 1559 ∣ x_seq (223^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_223_aux h_dvd
lemma dvd_227_aux : 227 ∣ x_seq 6581 := by
  have h_step : x_seq 6581 = x_seq (6581 - 1) * (2 + 6581 / Nat.gcd (x_seq (6581 - 1)) 6581) := by
    exact x_seq_step_eq_gen 6581 (by decide)
  have h_gcd : Nat.gcd (x_seq (6581 - 1)) 6581 = 1 := prime_not_dvd_x_seq_103 6581 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 6581 / 1 = 6581 := Nat.div_one 6581
  rw [h_div] at h_step
  have h_add : 2 + 6581 = 6583 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 227 ∣ 6583 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_227 : 227 ∣ x_seq (227^2 - 1) := by
  have h_dvd : x_seq 6581 ∣ x_seq (227^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_227_aux h_dvd
lemma dvd_229_aux : 229 ∣ x_seq 227 := by
  have h_step : x_seq 227 = x_seq (227 - 1) * (2 + 227 / Nat.gcd (x_seq (227 - 1)) 227) := by
    exact x_seq_step_eq_gen 227 (by decide)
  have h_gcd : Nat.gcd (x_seq (227 - 1)) 227 = 1 := prime_not_dvd_x_seq_103 227 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 227 / 1 = 227 := Nat.div_one 227
  rw [h_div] at h_step
  have h_add : 2 + 227 = 229 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 229 ∣ 229 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_229 : 229 ∣ x_seq (229^2 - 1) := by
  have h_dvd : x_seq 227 ∣ x_seq (229^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_229_aux h_dvd
lemma dvd_233_aux : 233 ∣ x_seq 1163 := by
  have h_step : x_seq 1163 = x_seq (1163 - 1) * (2 + 1163 / Nat.gcd (x_seq (1163 - 1)) 1163) := by
    exact x_seq_step_eq_gen 1163 (by decide)
  have h_gcd : Nat.gcd (x_seq (1163 - 1)) 1163 = 1 := prime_not_dvd_x_seq_103 1163 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1163 / 1 = 1163 := Nat.div_one 1163
  rw [h_div] at h_step
  have h_add : 2 + 1163 = 1165 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 233 ∣ 1165 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_233 : 233 ∣ x_seq (233^2 - 1) := by
  have h_dvd : x_seq 1163 ∣ x_seq (233^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_233_aux h_dvd
lemma dvd_239_aux : 239 ∣ x_seq 1193 := by
  have h_step : x_seq 1193 = x_seq (1193 - 1) * (2 + 1193 / Nat.gcd (x_seq (1193 - 1)) 1193) := by
    exact x_seq_step_eq_gen 1193 (by decide)
  have h_gcd : Nat.gcd (x_seq (1193 - 1)) 1193 = 1 := prime_not_dvd_x_seq_103 1193 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1193 / 1 = 1193 := Nat.div_one 1193
  rw [h_div] at h_step
  have h_add : 2 + 1193 = 1195 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 239 ∣ 1195 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_239 : 239 ∣ x_seq (239^2 - 1) := by
  have h_dvd : x_seq 1193 ∣ x_seq (239^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_239_aux h_dvd
lemma dvd_241_aux : 241 ∣ x_seq 239 := by
  have h_step : x_seq 239 = x_seq (239 - 1) * (2 + 239 / Nat.gcd (x_seq (239 - 1)) 239) := by
    exact x_seq_step_eq_gen 239 (by decide)
  have h_gcd : Nat.gcd (x_seq (239 - 1)) 239 = 1 := prime_not_dvd_x_seq_103 239 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 239 / 1 = 239 := Nat.div_one 239
  rw [h_div] at h_step
  have h_add : 2 + 239 = 241 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 241 ∣ 241 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_241 : 241 ∣ x_seq (241^2 - 1) := by
  have h_dvd : x_seq 239 ∣ x_seq (241^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_241_aux h_dvd
lemma dvd_251_aux : 251 ∣ x_seq 751 := by
  have h_step : x_seq 751 = x_seq (751 - 1) * (2 + 751 / Nat.gcd (x_seq (751 - 1)) 751) := by
    exact x_seq_step_eq_gen 751 (by decide)
  have h_gcd : Nat.gcd (x_seq (751 - 1)) 751 = 1 := prime_not_dvd_x_seq_103 751 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 751 / 1 = 751 := Nat.div_one 751
  rw [h_div] at h_step
  have h_add : 2 + 751 = 753 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 251 ∣ 753 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_251 : 251 ∣ x_seq (251^2 - 1) := by
  have h_dvd : x_seq 751 ∣ x_seq (251^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_251_aux h_dvd
lemma dvd_257_aux : 257 ∣ x_seq 769 := by
  have h_step : x_seq 769 = x_seq (769 - 1) * (2 + 769 / Nat.gcd (x_seq (769 - 1)) 769) := by
    exact x_seq_step_eq_gen 769 (by decide)
  have h_gcd : Nat.gcd (x_seq (769 - 1)) 769 = 1 := prime_not_dvd_x_seq_103 769 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 769 / 1 = 769 := Nat.div_one 769
  rw [h_div] at h_step
  have h_add : 2 + 769 = 771 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 257 ∣ 771 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_257 : 257 ∣ x_seq (257^2 - 1) := by
  have h_dvd : x_seq 769 ∣ x_seq (257^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_257_aux h_dvd
lemma dvd_263_aux : 263 ∣ x_seq 787 := by
  have h_step : x_seq 787 = x_seq (787 - 1) * (2 + 787 / Nat.gcd (x_seq (787 - 1)) 787) := by
    exact x_seq_step_eq_gen 787 (by decide)
  have h_gcd : Nat.gcd (x_seq (787 - 1)) 787 = 1 := prime_not_dvd_x_seq_103 787 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 787 / 1 = 787 := Nat.div_one 787
  rw [h_div] at h_step
  have h_add : 2 + 787 = 789 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 263 ∣ 789 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_263 : 263 ∣ x_seq (263^2 - 1) := by
  have h_dvd : x_seq 787 ∣ x_seq (263^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_263_aux h_dvd
lemma dvd_269_aux : 269 ∣ x_seq 2957 := by
  have h_step : x_seq 2957 = x_seq (2957 - 1) * (2 + 2957 / Nat.gcd (x_seq (2957 - 1)) 2957) := by
    exact x_seq_step_eq_gen 2957 (by decide)
  have h_gcd : Nat.gcd (x_seq (2957 - 1)) 2957 = 1 := prime_not_dvd_x_seq_103 2957 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 2957 / 1 = 2957 := Nat.div_one 2957
  rw [h_div] at h_step
  have h_add : 2 + 2957 = 2959 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 269 ∣ 2959 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_269 : 269 ∣ x_seq (269^2 - 1) := by
  have h_dvd : x_seq 2957 ∣ x_seq (269^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_269_aux h_dvd
lemma dvd_271_aux : 271 ∣ x_seq 269 := by
  have h_step : x_seq 269 = x_seq (269 - 1) * (2 + 269 / Nat.gcd (x_seq (269 - 1)) 269) := by
    exact x_seq_step_eq_gen 269 (by decide)
  have h_gcd : Nat.gcd (x_seq (269 - 1)) 269 = 1 := prime_not_dvd_x_seq_103 269 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 269 / 1 = 269 := Nat.div_one 269
  rw [h_div] at h_step
  have h_add : 2 + 269 = 271 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 271 ∣ 271 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_271 : 271 ∣ x_seq (271^2 - 1) := by
  have h_dvd : x_seq 269 ∣ x_seq (271^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_271_aux h_dvd
lemma dvd_277_aux : 277 ∣ x_seq 4153 := by
  have h_step : x_seq 4153 = x_seq (4153 - 1) * (2 + 4153 / Nat.gcd (x_seq (4153 - 1)) 4153) := by
    exact x_seq_step_eq_gen 4153 (by decide)
  have h_gcd : Nat.gcd (x_seq (4153 - 1)) 4153 = 1 := prime_not_dvd_x_seq_103 4153 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 4153 / 1 = 4153 := Nat.div_one 4153
  rw [h_div] at h_step
  have h_add : 2 + 4153 = 4155 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 277 ∣ 4155 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_277 : 277 ∣ x_seq (277^2 - 1) := by
  have h_dvd : x_seq 4153 ∣ x_seq (277^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_277_aux h_dvd
lemma dvd_281_aux : 281 ∣ x_seq 3089 := by
  have h_step : x_seq 3089 = x_seq (3089 - 1) * (2 + 3089 / Nat.gcd (x_seq (3089 - 1)) 3089) := by
    exact x_seq_step_eq_gen 3089 (by decide)
  have h_gcd : Nat.gcd (x_seq (3089 - 1)) 3089 = 1 := prime_not_dvd_x_seq_103 3089 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 3089 / 1 = 3089 := Nat.div_one 3089
  rw [h_div] at h_step
  have h_add : 2 + 3089 = 3091 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 281 ∣ 3091 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_281 : 281 ∣ x_seq (281^2 - 1) := by
  have h_dvd : x_seq 3089 ∣ x_seq (281^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_281_aux h_dvd
lemma dvd_283_aux : 283 ∣ x_seq 281 := by
  have h_step : x_seq 281 = x_seq (281 - 1) * (2 + 281 / Nat.gcd (x_seq (281 - 1)) 281) := by
    exact x_seq_step_eq_gen 281 (by decide)
  have h_gcd : Nat.gcd (x_seq (281 - 1)) 281 = 1 := prime_not_dvd_x_seq_103 281 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 281 / 1 = 281 := Nat.div_one 281
  rw [h_div] at h_step
  have h_add : 2 + 281 = 283 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 283 ∣ 283 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_283 : 283 ∣ x_seq (283^2 - 1) := by
  have h_dvd : x_seq 281 ∣ x_seq (283^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_283_aux h_dvd
lemma dvd_293_aux : 293 ∣ x_seq 877 := by
  have h_step : x_seq 877 = x_seq (877 - 1) * (2 + 877 / Nat.gcd (x_seq (877 - 1)) 877) := by
    exact x_seq_step_eq_gen 877 (by decide)
  have h_gcd : Nat.gcd (x_seq (877 - 1)) 877 = 1 := prime_not_dvd_x_seq_103 877 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 877 / 1 = 877 := Nat.div_one 877
  rw [h_div] at h_step
  have h_add : 2 + 877 = 879 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 293 ∣ 879 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_293 : 293 ∣ x_seq (293^2 - 1) := by
  have h_dvd : x_seq 877 ∣ x_seq (293^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_293_aux h_dvd
lemma dvd_307_aux : 307 ∣ x_seq 919 := by
  have h_step : x_seq 919 = x_seq (919 - 1) * (2 + 919 / Nat.gcd (x_seq (919 - 1)) 919) := by
    exact x_seq_step_eq_gen 919 (by decide)
  have h_gcd : Nat.gcd (x_seq (919 - 1)) 919 = 1 := prime_not_dvd_x_seq_103 919 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 919 / 1 = 919 := Nat.div_one 919
  rw [h_div] at h_step
  have h_add : 2 + 919 = 921 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 307 ∣ 921 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_307 : 307 ∣ x_seq (307^2 - 1) := by
  have h_dvd : x_seq 919 ∣ x_seq (307^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_307_aux h_dvd
lemma dvd_311_aux : 311 ∣ x_seq 1553 := by
  have h_step : x_seq 1553 = x_seq (1553 - 1) * (2 + 1553 / Nat.gcd (x_seq (1553 - 1)) 1553) := by
    exact x_seq_step_eq_gen 1553 (by decide)
  have h_gcd : Nat.gcd (x_seq (1553 - 1)) 1553 = 1 := prime_not_dvd_x_seq_103 1553 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1553 / 1 = 1553 := Nat.div_one 1553
  rw [h_div] at h_step
  have h_add : 2 + 1553 = 1555 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 311 ∣ 1555 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_311 : 311 ∣ x_seq (311^2 - 1) := by
  have h_dvd : x_seq 1553 ∣ x_seq (311^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_311_aux h_dvd
lemma dvd_313_aux : 313 ∣ x_seq 311 := by
  have h_step : x_seq 311 = x_seq (311 - 1) * (2 + 311 / Nat.gcd (x_seq (311 - 1)) 311) := by
    exact x_seq_step_eq_gen 311 (by decide)
  have h_gcd : Nat.gcd (x_seq (311 - 1)) 311 = 1 := prime_not_dvd_x_seq_103 311 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 311 / 1 = 311 := Nat.div_one 311
  rw [h_div] at h_step
  have h_add : 2 + 311 = 313 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 313 ∣ 313 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_313 : 313 ∣ x_seq (313^2 - 1) := by
  have h_dvd : x_seq 311 ∣ x_seq (313^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_313_aux h_dvd
lemma dvd_317_aux : 317 ∣ x_seq 1583 := by
  have h_step : x_seq 1583 = x_seq (1583 - 1) * (2 + 1583 / Nat.gcd (x_seq (1583 - 1)) 1583) := by
    exact x_seq_step_eq_gen 1583 (by decide)
  have h_gcd : Nat.gcd (x_seq (1583 - 1)) 1583 = 1 := prime_not_dvd_x_seq_103 1583 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 1583 / 1 = 1583 := Nat.div_one 1583
  rw [h_div] at h_step
  have h_add : 2 + 1583 = 1585 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 317 ∣ 1585 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_317 : 317 ∣ x_seq (317^2 - 1) := by
  have h_dvd : x_seq 1583 ∣ x_seq (317^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_317_aux h_dvd
lemma dvd_331_aux : 331 ∣ x_seq 991 := by
  have h_step : x_seq 991 = x_seq (991 - 1) * (2 + 991 / Nat.gcd (x_seq (991 - 1)) 991) := by
    exact x_seq_step_eq_gen 991 (by decide)
  have h_gcd : Nat.gcd (x_seq (991 - 1)) 991 = 1 := prime_not_dvd_x_seq_103 991 (by decide) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 991 / 1 = 991 := Nat.div_one 991
  rw [h_div] at h_step
  have h_add : 2 + 991 = 993 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_mr : 331 ∣ 993 := by decide
  exact dvd_mul_of_dvd_right h_dvd_mr _
lemma dvd_331 : 331 ∣ x_seq (331^2 - 1) := by
  have h_dvd : x_seq 991 ∣ x_seq (331^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_331_aux h_dvd
lemma prime_in_range_331 : ∀ r, r ≤ 331 → r > 103 → Nat.Prime r → r = 107 ∨ r = 109 ∨ r = 113 ∨ r = 127 ∨ r = 131 ∨ r = 137 ∨ r = 139 ∨ r = 149 ∨ r = 151 ∨ r = 157 ∨ r = 163 ∨ r = 167 ∨ r = 173 ∨ r = 179 ∨ r = 181 ∨ r = 191 ∨ r = 193 ∨ r = 197 ∨ r = 199 ∨ r = 211 ∨ r = 223 ∨ r = 227 ∨ r = 229 ∨ r = 233 ∨ r = 239 ∨ r = 241 ∨ r = 251 ∨ r = 257 ∨ r = 263 ∨ r = 269 ∨ r = 271 ∨ r = 277 ∨ r = 281 ∨ r = 283 ∨ r = 293 ∨ r = 307 ∨ r = 311 ∨ r = 313 ∨ r = 317 ∨ r = 331 := by
  decide

lemma prime_dvd_x_seq_sq_sub_one_bounded_331 (r : ℕ) (hr_le : r ≤ 331) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 103
  · exact prime_dvd_x_seq_sq_sub_one_bounded_103 r h_0 hr
  · have h_gt : r > 103 := by omega
    have h_cases := prime_in_range_331 r hr_le h_gt hr
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dvd_107
    · exact dvd_109
    · exact dvd_113
    · exact dvd_127
    · exact dvd_131
    · exact dvd_137
    · exact dvd_139
    · exact dvd_149
    · exact dvd_151
    · exact dvd_157
    · exact dvd_163
    · exact dvd_167
    · exact dvd_173
    · exact dvd_179
    · exact dvd_181
    · exact dvd_191
    · exact dvd_193
    · exact dvd_197
    · exact dvd_199
    · exact dvd_211
    · exact dvd_223
    · exact dvd_227
    · exact dvd_229
    · exact dvd_233
    · exact dvd_239
    · exact dvd_241
    · exact dvd_251
    · exact dvd_257
    · exact dvd_263
    · exact dvd_269
    · exact dvd_271
    · exact dvd_277
    · exact dvd_281
    · exact dvd_283
    · exact dvd_293
    · exact dvd_307
    · exact dvd_311
    · exact dvd_313
    · exact dvd_317
    · exact dvd_331

lemma prime_not_dvd_x_seq (p : ℕ) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  by_cases hp_lt2 : p < 113571
  · by_cases hp_lt_600 : p < 600
    · exact prime_not_dvd_x_seq_small p hp_lt_600 hp hp2
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
            have hg_pos : g > 0 := Nat.gcd_pos_of_pos_right _ hq_pos
            have hg_cases : g = 1 ∨ g > 1 := by omega
            rcases hg_cases with hg_eq1 | hg_gt1
            · clear h_dvd4
              have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
              set r := Nat.minFac (p - 2)
              have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
              have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
              have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
              have hr_le : r ≤ 331 := by
                by_contra h_gt
                have hr_ge_337 : r ≥ 337 := by
                  have : r ≠ 332 := by
                    intro h_eq
                    rw [h_eq] at hr_prime
                    exact (by decide : ¬ Nat.Prime 332) hr_prime
                  have : r ≠ 333 := by
                    intro h_eq
                    rw [h_eq] at hr_prime
                    exact (by decide : ¬ Nat.Prime 333) hr_prime
                  have : r ≠ 334 := by
                    intro h_eq
                    rw [h_eq] at hr_prime
                    exact (by decide : ¬ Nat.Prime 334) hr_prime
                  have : r ≠ 335 := by
                    intro h_eq
                    rw [h_eq] at hr_prime
                    exact (by decide : ¬ Nat.Prime 335) hr_prime
                  have : r ≠ 336 := by
                    intro h_eq
                    rw [h_eq] at hr_prime
                    exact (by decide : ¬ Nat.Prime 336) hr_prime
                  omega
                have : r^2 ≥ 113569 := by nlinarith
                have : p - 2 < 113569 := by omega
                omega
              have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_331 r hr_le hr_prime
              have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
              have h_r2_sub_1_pos : r^2 - 1 > 0 := by
                have : r ≥ 2 := Nat.Prime.two_le hr_prime
                have : r^2 ≥ 4 := by nlinarith
                omega
              have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
              have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
              have h_r_dvd_gcd : r ∣ g := Nat.dvd_gcd h_r_dvd_x hr_dvd
              rw [hg_eq1] at h_r_dvd_gcd
              have : r ∣ 1 := h_r_dvd_gcd
              have : r = 1 := Nat.eq_one_of_dvd_one this
              have : r ≥ 2 := Nat.Prime.two_le hr_prime
              omega
            · have hp_odd : p % 2 = 1 := by
                have : p % 2 ≠ 0 := by
                  intro h_even
                  have h_dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
                  have hp_eq : p = 2 := (hp.eq_one_or_self_of_dvd 2 h_dvd |>.resolve_left (by omega)).symm
                  omega
                omega
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
              have h_div_lt : (p - 2) / g < p - 2 := by
                apply Nat.div_lt_self
                · omega
                · omega
              have h_sum_lt : 2 + (p - 2) / g < p := by
                clear hp_odd hg_odd hg_ge3 hg_dvd h_dvd4
                omega
              have h_sum_pos : 2 + (p - 2) / g > 0 := by
                have : (p - 2) / g ≥ 0 := Nat.zero_le _
                omega
              have : p ≤ 2 + (p - 2) / g := Nat.le_of_dvd h_sum_pos h_dvd4
              omega
        · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
          have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
          contradiction
  · sorry

theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hp2
  rw [A135508_p_eq p hp]
  rw [prime_not_dvd_x_seq p hp hp2]
  exact Nat.div_one p
