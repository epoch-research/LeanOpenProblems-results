import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
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

lemma x_seq_step (idx : ℕ) (hidx : idx ≥ 2) : x_seq idx = 2 * x_seq (idx - 1) + Nat.lcm (x_seq (idx - 1)) idx := by
  have h_eq : idx = idx - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
  nth_rw 1 [h_eq]
  rw [x_seq]
  · have h_eq2 : idx - 1 + 1 = idx := Nat.sub_add_cancel (by omega)
    rw [h_eq2]
  · omega

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
| 0, _, acc => acc
| i + 1, idx, acc => x_seq_loop i (idx + 1) (2 * acc + Nat.lcm acc idx)

def x_seq_tail (n : ℕ) : ℕ :=
  if n = 0 then 0 else x_seq_loop (n - 1) 2 1

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
    exact ih (idx + 1) (2 * acc + Nat.lcm acc idx) h_idx' h_acc_eq

lemma x_seq_eq_x_seq_tail (n : ℕ) : x_seq n = x_seq_tail n := by
  unfold x_seq_tail
  split_ifs
  · subst n; rfl
  · have h_loop := x_seq_loop_lemma (n - 1) 2 1 (by omega) (by rfl)
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

lemma dvd_107_aux : 107 ∣ x_seq 2459 := by
      rw [x_seq_eq_x_seq_tail 2459]
      decide
lemma dvd_107 : 107 ∣ x_seq (107^2 - 1) := by
  have h_dvd : x_seq 2459 ∣ x_seq (107^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_107_aux h_dvd

lemma dvd_109_aux : 109 ∣ x_seq 107 := by
      rw [x_seq_eq_x_seq_tail 107]
      decide
lemma dvd_109 : 109 ∣ x_seq (109^2 - 1) := by
  have h_dvd : x_seq 107 ∣ x_seq (109^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_109_aux h_dvd

lemma dvd_113_aux : 113 ∣ x_seq 337 := by
      rw [x_seq_eq_x_seq_tail 337]
      decide
lemma dvd_113 : 113 ∣ x_seq (113^2 - 1) := by
  have h_dvd : x_seq 337 ∣ x_seq (113^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_113_aux h_dvd

lemma dvd_127_aux : 127 ∣ x_seq 379 := by
      rw [x_seq_eq_x_seq_tail 379]
      decide
lemma dvd_127 : 127 ∣ x_seq (127^2 - 1) := by
  have h_dvd : x_seq 379 ∣ x_seq (127^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_127_aux h_dvd

lemma dvd_131_aux : 131 ∣ x_seq 653 := by
      rw [x_seq_eq_x_seq_tail 653]
      decide
lemma dvd_131 : 131 ∣ x_seq (131^2 - 1) := by
  have h_dvd : x_seq 653 ∣ x_seq (131^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_131_aux h_dvd

lemma dvd_137_aux : 137 ∣ x_seq 409 := by
      rw [x_seq_eq_x_seq_tail 409]
      decide
lemma dvd_137 : 137 ∣ x_seq (137^2 - 1) := by
  have h_dvd : x_seq 409 ∣ x_seq (137^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_137_aux h_dvd

lemma dvd_139_aux : 139 ∣ x_seq 137 := by
      rw [x_seq_eq_x_seq_tail 137]
      decide
lemma dvd_139 : 139 ∣ x_seq (139^2 - 1) := by
  have h_dvd : x_seq 137 ∣ x_seq (139^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_139_aux h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_139 (r : ℕ) (hr_le : r ≤ 139) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
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
    · exact (by decide : ¬ Nat.Prime 104) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 105) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 106) hr |>.elim
    · exact dvd_107
    · exact (by decide : ¬ Nat.Prime 108) hr |>.elim
    · exact dvd_109
    · exact (by decide : ¬ Nat.Prime 110) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 111) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 112) hr |>.elim
    · exact dvd_113
    · exact (by decide : ¬ Nat.Prime 114) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 115) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 116) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 117) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 118) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 119) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 120) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 121) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 122) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 123) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 124) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 125) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 126) hr |>.elim
    · exact dvd_127
    · exact (by decide : ¬ Nat.Prime 128) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 129) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 130) hr |>.elim
    · exact dvd_131
    · exact (by decide : ¬ Nat.Prime 132) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 133) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 134) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 135) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 136) hr |>.elim
    · exact dvd_137
    · exact (by decide : ¬ Nat.Prime 138) hr |>.elim
    · exact dvd_139

lemma prime_not_dvd_x_seq_139 (p : ℕ) (hp_lt : p < 17163) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
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
            have hr_le : r ≤ 127 := by
              by_contra h_gt
              have hr_ge_128 : r ≥ 128 := by omega
              have hr_ge_131 : r ≥ 131 := by
                by_contra h_lt
                have : r = 128 ∨ r = 129 ∨ r = 130 := by omega
                rcases this with h_r | h_r | h_r
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 128) hr_prime |>.elim
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 129) hr_prime |>.elim
                · rw [h_r] at hr_prime
                  exact (by decide : ¬ Nat.Prime 130) hr_prime |>.elim
              have : r^2 ≥ 17161 := by nlinarith
              have : p - 2 < 17161 := by omega
              omega
            have hr_le_139 : r ≤ 139 := by omega
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_139 r hr_le_139 hr_prime
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
lemma dvd_helper (a b c : ℕ) (h : a ∣ b) : a ∣ c * b := dvd_mul_of_dvd_right h c

attribute [irreducible] x_seq

lemma gcd_149_aux (n : ℕ) (hn : n = 743) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 743 (by decide) (by norm_num) (by norm_num)
lemma dvd_149_aux (n : ℕ) (hn : n = 743) : 149 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 743 (by decide)
  rw [gcd_149_aux 743 rfl] at h
  have h_calc : 2 + 743 / 1 = 745 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 149 745 (x_seq (743 - 1)) (by decide)
lemma dvd_149 : 149 ∣ x_seq (149^2 - 1) := by
  have h_dvd : x_seq 743 ∣ x_seq (149^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_149_aux 743 rfl) h_dvd
lemma gcd_151_aux (n : ℕ) (hn : n = 149) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 149 (by decide) (by norm_num) (by norm_num)
lemma dvd_151_aux (n : ℕ) (hn : n = 149) : 151 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 149 (by decide)
  rw [gcd_151_aux 149 rfl] at h
  have h_calc : 2 + 149 / 1 = 151 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 151 151 (x_seq (149 - 1)) (by decide)
lemma dvd_151 : 151 ∣ x_seq (151^2 - 1) := by
  have h_dvd : x_seq 149 ∣ x_seq (151^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_151_aux 149 rfl) h_dvd
lemma gcd_157_aux (n : ℕ) (hn : n = 1097) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 1097 (by decide) (by norm_num) (by norm_num)
lemma dvd_157_aux (n : ℕ) (hn : n = 1097) : 157 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1097 (by decide)
  rw [gcd_157_aux 1097 rfl] at h
  have h_calc : 2 + 1097 / 1 = 1099 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 157 1099 (x_seq (1097 - 1)) (by decide)
lemma dvd_157 : 157 ∣ x_seq (157^2 - 1) := by
  have h_dvd : x_seq 1097 ∣ x_seq (157^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_157_aux 1097 rfl) h_dvd
lemma gcd_163_aux (n : ℕ) (hn : n = 487) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 487 (by decide) (by norm_num) (by norm_num)
lemma dvd_163_aux (n : ℕ) (hn : n = 487) : 163 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 487 (by decide)
  rw [gcd_163_aux 487 rfl] at h
  have h_calc : 2 + 487 / 1 = 489 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 163 489 (x_seq (487 - 1)) (by decide)
lemma dvd_163 : 163 ∣ x_seq (163^2 - 1) := by
  have h_dvd : x_seq 487 ∣ x_seq (163^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_163_aux 487 rfl) h_dvd
lemma gcd_167_aux (n : ℕ) (hn : n = 499) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 499 (by decide) (by norm_num) (by norm_num)
lemma dvd_167_aux (n : ℕ) (hn : n = 499) : 167 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 499 (by decide)
  rw [gcd_167_aux 499 rfl] at h
  have h_calc : 2 + 499 / 1 = 501 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 167 501 (x_seq (499 - 1)) (by decide)
lemma dvd_167 : 167 ∣ x_seq (167^2 - 1) := by
  have h_dvd : x_seq 499 ∣ x_seq (167^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_167_aux 499 rfl) h_dvd
lemma gcd_173_aux (n : ℕ) (hn : n = 863) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 863 (by decide) (by norm_num) (by norm_num)
lemma dvd_173_aux (n : ℕ) (hn : n = 863) : 173 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 863 (by decide)
  rw [gcd_173_aux 863 rfl] at h
  have h_calc : 2 + 863 / 1 = 865 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 173 865 (x_seq (863 - 1)) (by decide)
lemma dvd_173 : 173 ∣ x_seq (173^2 - 1) := by
  have h_dvd : x_seq 863 ∣ x_seq (173^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_173_aux 863 rfl) h_dvd
lemma gcd_179_aux (n : ℕ) (hn : n = 5189) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 5189 (by decide) (by norm_num) (by norm_num)
lemma dvd_179_aux (n : ℕ) (hn : n = 5189) : 179 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5189 (by decide)
  rw [gcd_179_aux 5189 rfl] at h
  have h_calc : 2 + 5189 / 1 = 5191 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 179 5191 (x_seq (5189 - 1)) (by decide)
lemma dvd_179 : 179 ∣ x_seq (179^2 - 1) := by
  have h_dvd : x_seq 5189 ∣ x_seq (179^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_179_aux 5189 rfl) h_dvd
lemma gcd_181_aux (n : ℕ) (hn : n = 179) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 179 (by decide) (by norm_num) (by norm_num)
lemma dvd_181_aux (n : ℕ) (hn : n = 179) : 181 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 179 (by decide)
  rw [gcd_181_aux 179 rfl] at h
  have h_calc : 2 + 179 / 1 = 181 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 181 181 (x_seq (179 - 1)) (by decide)
lemma dvd_181 : 181 ∣ x_seq (181^2 - 1) := by
  have h_dvd : x_seq 179 ∣ x_seq (181^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_181_aux 179 rfl) h_dvd
lemma gcd_191_aux (n : ℕ) (hn : n = 4391) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 4391 (by decide) (by norm_num) (by norm_num)
lemma dvd_191_aux (n : ℕ) (hn : n = 4391) : 191 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 4391 (by decide)
  rw [gcd_191_aux 4391 rfl] at h
  have h_calc : 2 + 4391 / 1 = 4393 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 191 4393 (x_seq (4391 - 1)) (by decide)
lemma dvd_191 : 191 ∣ x_seq (191^2 - 1) := by
  have h_dvd : x_seq 4391 ∣ x_seq (191^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_191_aux 4391 rfl) h_dvd
lemma gcd_193_aux (n : ℕ) (hn : n = 191) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 191 (by decide) (by norm_num) (by norm_num)
lemma dvd_193_aux (n : ℕ) (hn : n = 191) : 193 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 191 (by decide)
  rw [gcd_193_aux 191 rfl] at h
  have h_calc : 2 + 191 / 1 = 193 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 193 193 (x_seq (191 - 1)) (by decide)
lemma dvd_193 : 193 ∣ x_seq (193^2 - 1) := by
  have h_dvd : x_seq 191 ∣ x_seq (193^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_193_aux 191 rfl) h_dvd
lemma gcd_197_aux (n : ℕ) (hn : n = 983) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 983 (by decide) (by norm_num) (by norm_num)
lemma dvd_197_aux (n : ℕ) (hn : n = 983) : 197 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 983 (by decide)
  rw [gcd_197_aux 983 rfl] at h
  have h_calc : 2 + 983 / 1 = 985 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 197 985 (x_seq (983 - 1)) (by decide)
lemma dvd_197 : 197 ∣ x_seq (197^2 - 1) := by
  have h_dvd : x_seq 983 ∣ x_seq (197^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_197_aux 983 rfl) h_dvd
lemma gcd_199_aux (n : ℕ) (hn : n = 197) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 197 (by decide) (by norm_num) (by norm_num)
lemma dvd_199_aux (n : ℕ) (hn : n = 197) : 199 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 197 (by decide)
  rw [gcd_199_aux 197 rfl] at h
  have h_calc : 2 + 197 / 1 = 199 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 199 199 (x_seq (197 - 1)) (by decide)
lemma dvd_199 : 199 ∣ x_seq (199^2 - 1) := by
  have h_dvd : x_seq 197 ∣ x_seq (199^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_199_aux 197 rfl) h_dvd
lemma gcd_211_aux (n : ℕ) (hn : n = 631) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 631 (by decide) (by norm_num) (by norm_num)
lemma dvd_211_aux (n : ℕ) (hn : n = 631) : 211 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 631 (by decide)
  rw [gcd_211_aux 631 rfl] at h
  have h_calc : 2 + 631 / 1 = 633 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 211 633 (x_seq (631 - 1)) (by decide)
lemma dvd_211 : 211 ∣ x_seq (211^2 - 1) := by
  have h_dvd : x_seq 631 ∣ x_seq (211^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_211_aux 631 rfl) h_dvd
lemma gcd_223_aux (n : ℕ) (hn : n = 6911) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 6911 (by decide) (by norm_num) (by norm_num)
lemma dvd_223_aux (n : ℕ) (hn : n = 6911) : 223 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6911 (by decide)
  rw [gcd_223_aux 6911 rfl] at h
  have h_calc : 2 + 6911 / 1 = 6913 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 223 6913 (x_seq (6911 - 1)) (by decide)
lemma dvd_223 : 223 ∣ x_seq (223^2 - 1) := by
  have h_dvd : x_seq 6911 ∣ x_seq (223^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_223_aux 6911 rfl) h_dvd
lemma gcd_227_aux (n : ℕ) (hn : n = 6581) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 6581 (by decide) (by norm_num) (by norm_num)
lemma dvd_227_aux (n : ℕ) (hn : n = 6581) : 227 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6581 (by decide)
  rw [gcd_227_aux 6581 rfl] at h
  have h_calc : 2 + 6581 / 1 = 6583 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 227 6583 (x_seq (6581 - 1)) (by decide)
lemma dvd_227 : 227 ∣ x_seq (227^2 - 1) := by
  have h_dvd : x_seq 6581 ∣ x_seq (227^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_227_aux 6581 rfl) h_dvd
lemma gcd_229_aux (n : ℕ) (hn : n = 227) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 227 (by decide) (by norm_num) (by norm_num)
lemma dvd_229_aux (n : ℕ) (hn : n = 227) : 229 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 227 (by decide)
  rw [gcd_229_aux 227 rfl] at h
  have h_calc : 2 + 227 / 1 = 229 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 229 229 (x_seq (227 - 1)) (by decide)
lemma dvd_229 : 229 ∣ x_seq (229^2 - 1) := by
  have h_dvd : x_seq 227 ∣ x_seq (229^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_229_aux 227 rfl) h_dvd
lemma gcd_233_aux (n : ℕ) (hn : n = 1163) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 1163 (by decide) (by norm_num) (by norm_num)
lemma dvd_233_aux (n : ℕ) (hn : n = 1163) : 233 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1163 (by decide)
  rw [gcd_233_aux 1163 rfl] at h
  have h_calc : 2 + 1163 / 1 = 1165 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 233 1165 (x_seq (1163 - 1)) (by decide)
lemma dvd_233 : 233 ∣ x_seq (233^2 - 1) := by
  have h_dvd : x_seq 1163 ∣ x_seq (233^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_233_aux 1163 rfl) h_dvd
lemma gcd_239_aux (n : ℕ) (hn : n = 9319) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 9319 (by decide) (by norm_num) (by norm_num)
lemma dvd_239_aux (n : ℕ) (hn : n = 9319) : 239 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 9319 (by decide)
  rw [gcd_239_aux 9319 rfl] at h
  have h_calc : 2 + 9319 / 1 = 9321 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 239 9321 (x_seq (9319 - 1)) (by decide)
lemma dvd_239 : 239 ∣ x_seq (239^2 - 1) := by
  have h_dvd : x_seq 9319 ∣ x_seq (239^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_239_aux 9319 rfl) h_dvd
lemma gcd_241_aux (n : ℕ) (hn : n = 239) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 239 (by decide) (by norm_num) (by norm_num)
lemma dvd_241_aux (n : ℕ) (hn : n = 239) : 241 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 239 (by decide)
  rw [gcd_241_aux 239 rfl] at h
  have h_calc : 2 + 239 / 1 = 241 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 241 241 (x_seq (239 - 1)) (by decide)
lemma dvd_241 : 241 ∣ x_seq (241^2 - 1) := by
  have h_dvd : x_seq 239 ∣ x_seq (241^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_241_aux 239 rfl) h_dvd
lemma gcd_251_aux (n : ℕ) (hn : n = 751) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_139 751 (by decide) (by norm_num) (by norm_num)
lemma dvd_251_aux (n : ℕ) (hn : n = 751) : 251 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 751 (by decide)
  rw [gcd_251_aux 751 rfl] at h
  have h_calc : 2 + 751 / 1 = 753 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 251 753 (x_seq (751 - 1)) (by decide)
lemma dvd_251 : 251 ∣ x_seq (251^2 - 1) := by
  have h_dvd : x_seq 751 ∣ x_seq (251^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_251_aux 751 rfl) h_dvd
lemma prime_dvd_x_seq_sq_sub_one_bounded_251 (r : ℕ) (hr_le : r ≤ 251) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 139
  · exact prime_dvd_x_seq_sq_sub_one_bounded_139 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 140) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 141) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 142) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 143) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 144) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 145) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 146) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 147) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 148) hr |>.elim
    · exact dvd_149
    · exact (by decide : ¬ Nat.Prime 150) hr |>.elim
    · exact dvd_151
    · exact (by decide : ¬ Nat.Prime 152) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 153) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 154) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 155) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 156) hr |>.elim
    · exact dvd_157
    · exact (by decide : ¬ Nat.Prime 158) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 159) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 160) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 161) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 162) hr |>.elim
    · exact dvd_163
    · exact (by decide : ¬ Nat.Prime 164) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 165) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 166) hr |>.elim
    · exact dvd_167
    · exact (by decide : ¬ Nat.Prime 168) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 169) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 170) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 171) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 172) hr |>.elim
    · exact dvd_173
    · exact (by decide : ¬ Nat.Prime 174) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 175) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 176) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 177) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 178) hr |>.elim
    · exact dvd_179
    · exact (by decide : ¬ Nat.Prime 180) hr |>.elim
    · exact dvd_181
    · exact (by decide : ¬ Nat.Prime 182) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 183) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 184) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 185) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 186) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 187) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 188) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 189) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 190) hr |>.elim
    · exact dvd_191
    · exact (by decide : ¬ Nat.Prime 192) hr |>.elim
    · exact dvd_193
    · exact (by decide : ¬ Nat.Prime 194) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 195) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 196) hr |>.elim
    · exact dvd_197
    · exact (by decide : ¬ Nat.Prime 198) hr |>.elim
    · exact dvd_199
    · exact (by decide : ¬ Nat.Prime 200) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 201) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 202) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 203) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 204) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 205) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 206) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 207) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 208) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 209) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 210) hr |>.elim
    · exact dvd_211
    · exact (by decide : ¬ Nat.Prime 212) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 213) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 214) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 215) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 216) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 217) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 218) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 219) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 220) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 221) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 222) hr |>.elim
    · exact dvd_223
    · exact (by decide : ¬ Nat.Prime 224) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 225) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 226) hr |>.elim
    · exact dvd_227
    · exact (by decide : ¬ Nat.Prime 228) hr |>.elim
    · exact dvd_229
    · exact (by decide : ¬ Nat.Prime 230) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 231) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 232) hr |>.elim
    · exact dvd_233
    · exact (by decide : ¬ Nat.Prime 234) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 235) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 236) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 237) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 238) hr |>.elim
    · exact dvd_239
    · exact (by decide : ¬ Nat.Prime 240) hr |>.elim
    · exact dvd_241
    · exact (by decide : ¬ Nat.Prime 242) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 243) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 244) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 245) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 246) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 247) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 248) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 249) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 250) hr |>.elim
    · exact dvd_251

lemma prime_not_dvd_x_seq_251 (p : ℕ) (hp_lt : p < 66048) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
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
            have hr_le : r ≤ 251 := by
              by_contra h_gt
              have hr_ge : r ≥ 252 := by omega
              have hr_lt_257 : r < 257 := by
                by_contra h_ge'
                have : r ≥ 257 := by omega
                have : r^2 ≥ 66049 := by nlinarith
                omega
              interval_cases r
              · exact (by decide : ¬ Nat.Prime 252) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 253) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 254) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 255) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 256) hr_prime |>.elim
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_251 r hr_le hr_prime
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
lemma gcd_257_aux (n : ℕ) (hn : n = 769) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 769 (by decide) (by norm_num) (by norm_num)
lemma dvd_257_aux (n : ℕ) (hn : n = 769) : 257 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 769 (by decide)
  rw [gcd_257_aux 769 rfl] at h
  have h_calc : 2 + 769 / 1 = 771 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 257 771 (x_seq (769 - 1)) (by decide)
lemma dvd_257 : 257 ∣ x_seq (257^2 - 1) := by
  have h_dvd : x_seq 769 ∣ x_seq (257^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_257_aux 769 rfl) h_dvd
lemma gcd_263_aux (n : ℕ) (hn : n = 787) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 787 (by decide) (by norm_num) (by norm_num)
lemma dvd_263_aux (n : ℕ) (hn : n = 787) : 263 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 787 (by decide)
  rw [gcd_263_aux 787 rfl] at h
  have h_calc : 2 + 787 / 1 = 789 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 263 789 (x_seq (787 - 1)) (by decide)
lemma dvd_263 : 263 ∣ x_seq (263^2 - 1) := by
  have h_dvd : x_seq 787 ∣ x_seq (263^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_263_aux 787 rfl) h_dvd
lemma gcd_269_aux (n : ℕ) (hn : n = 2957) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 2957 (by decide) (by norm_num) (by norm_num)
lemma dvd_269_aux (n : ℕ) (hn : n = 2957) : 269 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2957 (by decide)
  rw [gcd_269_aux 2957 rfl] at h
  have h_calc : 2 + 2957 / 1 = 2959 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 269 2959 (x_seq (2957 - 1)) (by decide)
lemma dvd_269 : 269 ∣ x_seq (269^2 - 1) := by
  have h_dvd : x_seq 2957 ∣ x_seq (269^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_269_aux 2957 rfl) h_dvd
lemma gcd_271_aux (n : ℕ) (hn : n = 269) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 269 (by decide) (by norm_num) (by norm_num)
lemma dvd_271_aux (n : ℕ) (hn : n = 269) : 271 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 269 (by decide)
  rw [gcd_271_aux 269 rfl] at h
  have h_calc : 2 + 269 / 1 = 271 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 271 271 (x_seq (269 - 1)) (by decide)
lemma dvd_271 : 271 ∣ x_seq (271^2 - 1) := by
  have h_dvd : x_seq 269 ∣ x_seq (271^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_271_aux 269 rfl) h_dvd
lemma gcd_277_aux (n : ℕ) (hn : n = 7477) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 7477 (by decide) (by norm_num) (by norm_num)
lemma dvd_277_aux (n : ℕ) (hn : n = 7477) : 277 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7477 (by decide)
  rw [gcd_277_aux 7477 rfl] at h
  have h_calc : 2 + 7477 / 1 = 7479 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 277 7479 (x_seq (7477 - 1)) (by decide)
lemma dvd_277 : 277 ∣ x_seq (277^2 - 1) := by
  have h_dvd : x_seq 7477 ∣ x_seq (277^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_277_aux 7477 rfl) h_dvd
lemma gcd_281_aux (n : ℕ) (hn : n = 3089) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 3089 (by decide) (by norm_num) (by norm_num)
lemma dvd_281_aux (n : ℕ) (hn : n = 3089) : 281 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3089 (by decide)
  rw [gcd_281_aux 3089 rfl] at h
  have h_calc : 2 + 3089 / 1 = 3091 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 281 3091 (x_seq (3089 - 1)) (by decide)
lemma dvd_281 : 281 ∣ x_seq (281^2 - 1) := by
  have h_dvd : x_seq 3089 ∣ x_seq (281^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_281_aux 3089 rfl) h_dvd
lemma gcd_283_aux (n : ℕ) (hn : n = 281) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 281 (by decide) (by norm_num) (by norm_num)
lemma dvd_283_aux (n : ℕ) (hn : n = 281) : 283 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 281 (by decide)
  rw [gcd_283_aux 281 rfl] at h
  have h_calc : 2 + 281 / 1 = 283 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 283 283 (x_seq (281 - 1)) (by decide)
lemma dvd_283 : 283 ∣ x_seq (283^2 - 1) := by
  have h_dvd : x_seq 281 ∣ x_seq (283^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_283_aux 281 rfl) h_dvd
lemma gcd_293_aux (n : ℕ) (hn : n = 877) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 877 (by decide) (by norm_num) (by norm_num)
lemma dvd_293_aux (n : ℕ) (hn : n = 877) : 293 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 877 (by decide)
  rw [gcd_293_aux 877 rfl] at h
  have h_calc : 2 + 877 / 1 = 879 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 293 879 (x_seq (877 - 1)) (by decide)
lemma dvd_293 : 293 ∣ x_seq (293^2 - 1) := by
  have h_dvd : x_seq 877 ∣ x_seq (293^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_293_aux 877 rfl) h_dvd
lemma gcd_307_aux (n : ℕ) (hn : n = 919) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 919 (by decide) (by norm_num) (by norm_num)
lemma dvd_307_aux (n : ℕ) (hn : n = 919) : 307 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 919 (by decide)
  rw [gcd_307_aux 919 rfl] at h
  have h_calc : 2 + 919 / 1 = 921 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 307 921 (x_seq (919 - 1)) (by decide)
lemma dvd_307 : 307 ∣ x_seq (307^2 - 1) := by
  have h_dvd : x_seq 919 ∣ x_seq (307^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_307_aux 919 rfl) h_dvd
lemma gcd_311_aux (n : ℕ) (hn : n = 1553) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1553 (by decide) (by norm_num) (by norm_num)
lemma dvd_311_aux (n : ℕ) (hn : n = 1553) : 311 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1553 (by decide)
  rw [gcd_311_aux 1553 rfl] at h
  have h_calc : 2 + 1553 / 1 = 1555 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 311 1555 (x_seq (1553 - 1)) (by decide)
lemma dvd_311 : 311 ∣ x_seq (311^2 - 1) := by
  have h_dvd : x_seq 1553 ∣ x_seq (311^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_311_aux 1553 rfl) h_dvd
lemma gcd_313_aux (n : ℕ) (hn : n = 311) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 311 (by decide) (by norm_num) (by norm_num)
lemma dvd_313_aux (n : ℕ) (hn : n = 311) : 313 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 311 (by decide)
  rw [gcd_313_aux 311 rfl] at h
  have h_calc : 2 + 311 / 1 = 313 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 313 313 (x_seq (311 - 1)) (by decide)
lemma dvd_313 : 313 ∣ x_seq (313^2 - 1) := by
  have h_dvd : x_seq 311 ∣ x_seq (313^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_313_aux 311 rfl) h_dvd
lemma gcd_317_aux (n : ℕ) (hn : n = 1583) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1583 (by decide) (by norm_num) (by norm_num)
lemma dvd_317_aux (n : ℕ) (hn : n = 1583) : 317 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1583 (by decide)
  rw [gcd_317_aux 1583 rfl] at h
  have h_calc : 2 + 1583 / 1 = 1585 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 317 1585 (x_seq (1583 - 1)) (by decide)
lemma dvd_317 : 317 ∣ x_seq (317^2 - 1) := by
  have h_dvd : x_seq 1583 ∣ x_seq (317^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_317_aux 1583 rfl) h_dvd
lemma gcd_331_aux (n : ℕ) (hn : n = 991) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 991 (by decide) (by norm_num) (by norm_num)
lemma dvd_331_aux (n : ℕ) (hn : n = 991) : 331 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 991 (by decide)
  rw [gcd_331_aux 991 rfl] at h
  have h_calc : 2 + 991 / 1 = 993 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 331 993 (x_seq (991 - 1)) (by decide)
lemma dvd_331 : 331 ∣ x_seq (331^2 - 1) := by
  have h_dvd : x_seq 991 ∣ x_seq (331^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_331_aux 991 rfl) h_dvd
lemma gcd_337_aux (n : ℕ) (hn : n = 1009) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1009 (by decide) (by norm_num) (by norm_num)
lemma dvd_337_aux (n : ℕ) (hn : n = 1009) : 337 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1009 (by decide)
  rw [gcd_337_aux 1009 rfl] at h
  have h_calc : 2 + 1009 / 1 = 1011 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 337 1011 (x_seq (1009 - 1)) (by decide)
lemma dvd_337 : 337 ∣ x_seq (337^2 - 1) := by
  have h_dvd : x_seq 1009 ∣ x_seq (337^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_337_aux 1009 rfl) h_dvd
lemma gcd_347_aux (n : ℕ) (hn : n = 1039) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1039 (by decide) (by norm_num) (by norm_num)
lemma dvd_347_aux (n : ℕ) (hn : n = 1039) : 347 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1039 (by decide)
  rw [gcd_347_aux 1039 rfl] at h
  have h_calc : 2 + 1039 / 1 = 1041 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 347 1041 (x_seq (1039 - 1)) (by decide)
lemma dvd_347 : 347 ∣ x_seq (347^2 - 1) := by
  have h_dvd : x_seq 1039 ∣ x_seq (347^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_347_aux 1039 rfl) h_dvd
lemma gcd_349_aux (n : ℕ) (hn : n = 347) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 347 (by decide) (by norm_num) (by norm_num)
lemma dvd_349_aux (n : ℕ) (hn : n = 347) : 349 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 347 (by decide)
  rw [gcd_349_aux 347 rfl] at h
  have h_calc : 2 + 347 / 1 = 349 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 349 349 (x_seq (347 - 1)) (by decide)
lemma dvd_349 : 349 ∣ x_seq (349^2 - 1) := by
  have h_dvd : x_seq 347 ∣ x_seq (349^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_349_aux 347 rfl) h_dvd
lemma gcd_353_aux (n : ℕ) (hn : n = 7411) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 7411 (by decide) (by norm_num) (by norm_num)
lemma dvd_353_aux (n : ℕ) (hn : n = 7411) : 353 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7411 (by decide)
  rw [gcd_353_aux 7411 rfl] at h
  have h_calc : 2 + 7411 / 1 = 7413 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 353 7413 (x_seq (7411 - 1)) (by decide)
lemma dvd_353 : 353 ∣ x_seq (353^2 - 1) := by
  have h_dvd : x_seq 7411 ∣ x_seq (353^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_353_aux 7411 rfl) h_dvd
lemma gcd_359_aux (n : ℕ) (hn : n = 6101) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 6101 (by decide) (by norm_num) (by norm_num)
lemma dvd_359_aux (n : ℕ) (hn : n = 6101) : 359 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6101 (by decide)
  rw [gcd_359_aux 6101 rfl] at h
  have h_calc : 2 + 6101 / 1 = 6103 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 359 6103 (x_seq (6101 - 1)) (by decide)
lemma dvd_359 : 359 ∣ x_seq (359^2 - 1) := by
  have h_dvd : x_seq 6101 ∣ x_seq (359^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_359_aux 6101 rfl) h_dvd
lemma gcd_367_aux (n : ℕ) (hn : n = 6971) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 6971 (by decide) (by norm_num) (by norm_num)
lemma dvd_367_aux (n : ℕ) (hn : n = 6971) : 367 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6971 (by decide)
  rw [gcd_367_aux 6971 rfl] at h
  have h_calc : 2 + 6971 / 1 = 6973 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 367 6973 (x_seq (6971 - 1)) (by decide)
lemma dvd_367 : 367 ∣ x_seq (367^2 - 1) := by
  have h_dvd : x_seq 6971 ∣ x_seq (367^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_367_aux 6971 rfl) h_dvd
lemma gcd_373_aux (n : ℕ) (hn : n = 1117) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1117 (by decide) (by norm_num) (by norm_num)
lemma dvd_373_aux (n : ℕ) (hn : n = 1117) : 373 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1117 (by decide)
  rw [gcd_373_aux 1117 rfl] at h
  have h_calc : 2 + 1117 / 1 = 1119 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 373 1119 (x_seq (1117 - 1)) (by decide)
lemma dvd_373 : 373 ∣ x_seq (373^2 - 1) := by
  have h_dvd : x_seq 1117 ∣ x_seq (373^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_373_aux 1117 rfl) h_dvd
lemma gcd_379_aux (n : ℕ) (hn : n = 5683) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 5683 (by decide) (by norm_num) (by norm_num)
lemma dvd_379_aux (n : ℕ) (hn : n = 5683) : 379 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5683 (by decide)
  rw [gcd_379_aux 5683 rfl] at h
  have h_calc : 2 + 5683 / 1 = 5685 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 379 5685 (x_seq (5683 - 1)) (by decide)
lemma dvd_379 : 379 ∣ x_seq (379^2 - 1) := by
  have h_dvd : x_seq 5683 ∣ x_seq (379^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_379_aux 5683 rfl) h_dvd
lemma gcd_383_aux (n : ℕ) (hn : n = 1913) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1913 (by decide) (by norm_num) (by norm_num)
lemma dvd_383_aux (n : ℕ) (hn : n = 1913) : 383 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1913 (by decide)
  rw [gcd_383_aux 1913 rfl] at h
  have h_calc : 2 + 1913 / 1 = 1915 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 383 1915 (x_seq (1913 - 1)) (by decide)
lemma dvd_383 : 383 ∣ x_seq (383^2 - 1) := by
  have h_dvd : x_seq 1913 ∣ x_seq (383^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_383_aux 1913 rfl) h_dvd
lemma gcd_389_aux (n : ℕ) (hn : n = 8167) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 8167 (by decide) (by norm_num) (by norm_num)
lemma dvd_389_aux (n : ℕ) (hn : n = 8167) : 389 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 8167 (by decide)
  rw [gcd_389_aux 8167 rfl] at h
  have h_calc : 2 + 8167 / 1 = 8169 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 389 8169 (x_seq (8167 - 1)) (by decide)
lemma dvd_389 : 389 ∣ x_seq (389^2 - 1) := by
  have h_dvd : x_seq 8167 ∣ x_seq (389^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_389_aux 8167 rfl) h_dvd
lemma gcd_397_aux (n : ℕ) (hn : n = 2777) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 2777 (by decide) (by norm_num) (by norm_num)
lemma dvd_397_aux (n : ℕ) (hn : n = 2777) : 397 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2777 (by decide)
  rw [gcd_397_aux 2777 rfl] at h
  have h_calc : 2 + 2777 / 1 = 2779 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 397 2779 (x_seq (2777 - 1)) (by decide)
lemma dvd_397 : 397 ∣ x_seq (397^2 - 1) := by
  have h_dvd : x_seq 2777 ∣ x_seq (397^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_397_aux 2777 rfl) h_dvd
lemma gcd_401_aux (n : ℕ) (hn : n = 1201) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1201 (by decide) (by norm_num) (by norm_num)
lemma dvd_401_aux (n : ℕ) (hn : n = 1201) : 401 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1201 (by decide)
  rw [gcd_401_aux 1201 rfl] at h
  have h_calc : 2 + 1201 / 1 = 1203 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 401 1203 (x_seq (1201 - 1)) (by decide)
lemma dvd_401 : 401 ∣ x_seq (401^2 - 1) := by
  have h_dvd : x_seq 1201 ∣ x_seq (401^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_401_aux 1201 rfl) h_dvd
lemma gcd_409_aux (n : ℕ) (hn : n = 15131) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 15131 (by decide) (by norm_num) (by norm_num)
lemma dvd_409_aux (n : ℕ) (hn : n = 15131) : 409 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 15131 (by decide)
  rw [gcd_409_aux 15131 rfl] at h
  have h_calc : 2 + 15131 / 1 = 15133 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 409 15133 (x_seq (15131 - 1)) (by decide)
lemma dvd_409 : 409 ∣ x_seq (409^2 - 1) := by
  have h_dvd : x_seq 15131 ∣ x_seq (409^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_409_aux 15131 rfl) h_dvd
lemma gcd_419_aux (n : ℕ) (hn : n = 7121) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 7121 (by decide) (by norm_num) (by norm_num)
lemma dvd_419_aux (n : ℕ) (hn : n = 7121) : 419 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7121 (by decide)
  rw [gcd_419_aux 7121 rfl] at h
  have h_calc : 2 + 7121 / 1 = 7123 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 419 7123 (x_seq (7121 - 1)) (by decide)
lemma dvd_419 : 419 ∣ x_seq (419^2 - 1) := by
  have h_dvd : x_seq 7121 ∣ x_seq (419^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_419_aux 7121 rfl) h_dvd
lemma gcd_421_aux (n : ℕ) (hn : n = 419) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 419 (by decide) (by norm_num) (by norm_num)
lemma dvd_421_aux (n : ℕ) (hn : n = 419) : 421 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 419 (by decide)
  rw [gcd_421_aux 419 rfl] at h
  have h_calc : 2 + 419 / 1 = 421 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 421 421 (x_seq (419 - 1)) (by decide)
lemma dvd_421 : 421 ∣ x_seq (421^2 - 1) := by
  have h_dvd : x_seq 419 ∣ x_seq (421^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_421_aux 419 rfl) h_dvd
lemma gcd_431_aux (n : ℕ) (hn : n = 2153) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 2153 (by decide) (by norm_num) (by norm_num)
lemma dvd_431_aux (n : ℕ) (hn : n = 2153) : 431 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2153 (by decide)
  rw [gcd_431_aux 2153 rfl] at h
  have h_calc : 2 + 2153 / 1 = 2155 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 431 2155 (x_seq (2153 - 1)) (by decide)
lemma dvd_431 : 431 ∣ x_seq (431^2 - 1) := by
  have h_dvd : x_seq 2153 ∣ x_seq (431^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_431_aux 2153 rfl) h_dvd
lemma gcd_433_aux (n : ℕ) (hn : n = 431) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 431 (by decide) (by norm_num) (by norm_num)
lemma dvd_433_aux (n : ℕ) (hn : n = 431) : 433 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 431 (by decide)
  rw [gcd_433_aux 431 rfl] at h
  have h_calc : 2 + 431 / 1 = 433 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 433 433 (x_seq (431 - 1)) (by decide)
lemma dvd_433 : 433 ∣ x_seq (433^2 - 1) := by
  have h_dvd : x_seq 431 ∣ x_seq (433^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_433_aux 431 rfl) h_dvd
lemma gcd_439_aux (n : ℕ) (hn : n = 10973) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 10973 (by decide) (by norm_num) (by norm_num)
lemma dvd_439_aux (n : ℕ) (hn : n = 10973) : 439 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 10973 (by decide)
  rw [gcd_439_aux 10973 rfl] at h
  have h_calc : 2 + 10973 / 1 = 10975 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 439 10975 (x_seq (10973 - 1)) (by decide)
lemma dvd_439 : 439 ∣ x_seq (439^2 - 1) := by
  have h_dvd : x_seq 10973 ∣ x_seq (439^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_439_aux 10973 rfl) h_dvd
lemma gcd_443_aux (n : ℕ) (hn : n = 1327) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1327 (by decide) (by norm_num) (by norm_num)
lemma dvd_443_aux (n : ℕ) (hn : n = 1327) : 443 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1327 (by decide)
  rw [gcd_443_aux 1327 rfl] at h
  have h_calc : 2 + 1327 / 1 = 1329 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 443 1329 (x_seq (1327 - 1)) (by decide)
lemma dvd_443 : 443 ∣ x_seq (443^2 - 1) := by
  have h_dvd : x_seq 1327 ∣ x_seq (443^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_443_aux 1327 rfl) h_dvd
lemma gcd_449_aux (n : ℕ) (hn : n = 2243) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 2243 (by decide) (by norm_num) (by norm_num)
lemma dvd_449_aux (n : ℕ) (hn : n = 2243) : 449 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2243 (by decide)
  rw [gcd_449_aux 2243 rfl] at h
  have h_calc : 2 + 2243 / 1 = 2245 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 449 2245 (x_seq (2243 - 1)) (by decide)
lemma dvd_449 : 449 ∣ x_seq (449^2 - 1) := by
  have h_dvd : x_seq 2243 ∣ x_seq (449^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_449_aux 2243 rfl) h_dvd
lemma gcd_457_aux (n : ℕ) (hn : n = 11423) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 11423 (by decide) (by norm_num) (by norm_num)
lemma dvd_457_aux (n : ℕ) (hn : n = 11423) : 457 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 11423 (by decide)
  rw [gcd_457_aux 11423 rfl] at h
  have h_calc : 2 + 11423 / 1 = 11425 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 457 11425 (x_seq (11423 - 1)) (by decide)
lemma dvd_457 : 457 ∣ x_seq (457^2 - 1) := by
  have h_dvd : x_seq 11423 ∣ x_seq (457^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_457_aux 11423 rfl) h_dvd
lemma gcd_461_aux (n : ℕ) (hn : n = 1381) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1381 (by decide) (by norm_num) (by norm_num)
lemma dvd_461_aux (n : ℕ) (hn : n = 1381) : 461 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1381 (by decide)
  rw [gcd_461_aux 1381 rfl] at h
  have h_calc : 2 + 1381 / 1 = 1383 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 461 1383 (x_seq (1381 - 1)) (by decide)
lemma dvd_461 : 461 ∣ x_seq (461^2 - 1) := by
  have h_dvd : x_seq 1381 ∣ x_seq (461^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_461_aux 1381 rfl) h_dvd
lemma gcd_463_aux (n : ℕ) (hn : n = 461) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 461 (by decide) (by norm_num) (by norm_num)
lemma dvd_463_aux (n : ℕ) (hn : n = 461) : 463 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 461 (by decide)
  rw [gcd_463_aux 461 rfl] at h
  have h_calc : 2 + 461 / 1 = 463 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 463 463 (x_seq (461 - 1)) (by decide)
lemma dvd_463 : 463 ∣ x_seq (463^2 - 1) := by
  have h_dvd : x_seq 461 ∣ x_seq (463^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_463_aux 461 rfl) h_dvd
lemma gcd_467_aux (n : ℕ) (hn : n = 1399) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1399 (by decide) (by norm_num) (by norm_num)
lemma dvd_467_aux (n : ℕ) (hn : n = 1399) : 467 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1399 (by decide)
  rw [gcd_467_aux 1399 rfl] at h
  have h_calc : 2 + 1399 / 1 = 1401 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 467 1401 (x_seq (1399 - 1)) (by decide)
lemma dvd_467 : 467 ∣ x_seq (467^2 - 1) := by
  have h_dvd : x_seq 1399 ∣ x_seq (467^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_467_aux 1399 rfl) h_dvd
lemma gcd_479_aux (n : ℕ) (hn : n = 16763) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 16763 (by decide) (by norm_num) (by norm_num)
lemma dvd_479_aux (n : ℕ) (hn : n = 16763) : 479 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 16763 (by decide)
  rw [gcd_479_aux 16763 rfl] at h
  have h_calc : 2 + 16763 / 1 = 16765 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 479 16765 (x_seq (16763 - 1)) (by decide)
lemma dvd_479 : 479 ∣ x_seq (479^2 - 1) := by
  have h_dvd : x_seq 16763 ∣ x_seq (479^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_479_aux 16763 rfl) h_dvd
lemma gcd_487_aux (n : ℕ) (hn : n = 1459) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1459 (by decide) (by norm_num) (by norm_num)
lemma dvd_487_aux (n : ℕ) (hn : n = 1459) : 487 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1459 (by decide)
  rw [gcd_487_aux 1459 rfl] at h
  have h_calc : 2 + 1459 / 1 = 1461 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 487 1461 (x_seq (1459 - 1)) (by decide)
lemma dvd_487 : 487 ∣ x_seq (487^2 - 1) := by
  have h_dvd : x_seq 1459 ∣ x_seq (487^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_487_aux 1459 rfl) h_dvd
lemma gcd_491_aux (n : ℕ) (hn : n = 1471) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 1471 (by decide) (by norm_num) (by norm_num)
lemma dvd_491_aux (n : ℕ) (hn : n = 1471) : 491 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1471 (by decide)
  rw [gcd_491_aux 1471 rfl] at h
  have h_calc : 2 + 1471 / 1 = 1473 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 491 1473 (x_seq (1471 - 1)) (by decide)
lemma dvd_491 : 491 ∣ x_seq (491^2 - 1) := by
  have h_dvd : x_seq 1471 ∣ x_seq (491^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_491_aux 1471 rfl) h_dvd
lemma gcd_499_aux (n : ℕ) (hn : n = 9479) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 9479 (by decide) (by norm_num) (by norm_num)
lemma dvd_499_aux (n : ℕ) (hn : n = 9479) : 499 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 9479 (by decide)
  rw [gcd_499_aux 9479 rfl] at h
  have h_calc : 2 + 9479 / 1 = 9481 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 499 9481 (x_seq (9479 - 1)) (by decide)
lemma dvd_499 : 499 ∣ x_seq (499^2 - 1) := by
  have h_dvd : x_seq 9479 ∣ x_seq (499^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_499_aux 9479 rfl) h_dvd
lemma gcd_503_aux (n : ℕ) (hn : n = 5531) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 5531 (by decide) (by norm_num) (by norm_num)
lemma dvd_503_aux (n : ℕ) (hn : n = 5531) : 503 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5531 (by decide)
  rw [gcd_503_aux 5531 rfl] at h
  have h_calc : 2 + 5531 / 1 = 5533 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 503 5533 (x_seq (5531 - 1)) (by decide)
lemma dvd_503 : 503 ∣ x_seq (503^2 - 1) := by
  have h_dvd : x_seq 5531 ∣ x_seq (503^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_503_aux 5531 rfl) h_dvd
lemma gcd_509_aux (n : ℕ) (hn : n = 2543) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_251 2543 (by decide) (by norm_num) (by norm_num)
lemma dvd_509_aux (n : ℕ) (hn : n = 2543) : 509 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2543 (by decide)
  rw [gcd_509_aux 2543 rfl] at h
  have h_calc : 2 + 2543 / 1 = 2545 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 509 2545 (x_seq (2543 - 1)) (by decide)
lemma dvd_509 : 509 ∣ x_seq (509^2 - 1) := by
  have h_dvd : x_seq 2543 ∣ x_seq (509^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_509_aux 2543 rfl) h_dvd
lemma prime_dvd_x_seq_sq_sub_one_bounded_509 (r : ℕ) (hr_le : r ≤ 509) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 251
  · exact prime_dvd_x_seq_sq_sub_one_bounded_251 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 252) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 253) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 254) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 255) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 256) hr |>.elim
    · exact dvd_257
    · exact (by decide : ¬ Nat.Prime 258) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 259) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 260) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 261) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 262) hr |>.elim
    · exact dvd_263
    · exact (by decide : ¬ Nat.Prime 264) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 265) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 266) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 267) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 268) hr |>.elim
    · exact dvd_269
    · exact (by decide : ¬ Nat.Prime 270) hr |>.elim
    · exact dvd_271
    · exact (by decide : ¬ Nat.Prime 272) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 273) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 274) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 275) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 276) hr |>.elim
    · exact dvd_277
    · exact (by decide : ¬ Nat.Prime 278) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 279) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 280) hr |>.elim
    · exact dvd_281
    · exact (by decide : ¬ Nat.Prime 282) hr |>.elim
    · exact dvd_283
    · exact (by decide : ¬ Nat.Prime 284) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 285) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 286) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 287) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 288) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 289) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 290) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 291) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 292) hr |>.elim
    · exact dvd_293
    · exact (by decide : ¬ Nat.Prime 294) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 295) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 296) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 297) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 298) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 299) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 300) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 301) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 302) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 303) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 304) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 305) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 306) hr |>.elim
    · exact dvd_307
    · exact (by decide : ¬ Nat.Prime 308) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 309) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 310) hr |>.elim
    · exact dvd_311
    · exact (by decide : ¬ Nat.Prime 312) hr |>.elim
    · exact dvd_313
    · exact (by decide : ¬ Nat.Prime 314) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 315) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 316) hr |>.elim
    · exact dvd_317
    · exact (by decide : ¬ Nat.Prime 318) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 319) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 320) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 321) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 322) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 323) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 324) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 325) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 326) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 327) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 328) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 329) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 330) hr |>.elim
    · exact dvd_331
    · exact (by decide : ¬ Nat.Prime 332) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 333) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 334) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 335) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 336) hr |>.elim
    · exact dvd_337
    · exact (by decide : ¬ Nat.Prime 338) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 339) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 340) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 341) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 342) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 343) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 344) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 345) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 346) hr |>.elim
    · exact dvd_347
    · exact (by decide : ¬ Nat.Prime 348) hr |>.elim
    · exact dvd_349
    · exact (by decide : ¬ Nat.Prime 350) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 351) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 352) hr |>.elim
    · exact dvd_353
    · exact (by decide : ¬ Nat.Prime 354) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 355) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 356) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 357) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 358) hr |>.elim
    · exact dvd_359
    · exact (by decide : ¬ Nat.Prime 360) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 361) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 362) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 363) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 364) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 365) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 366) hr |>.elim
    · exact dvd_367
    · exact (by decide : ¬ Nat.Prime 368) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 369) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 370) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 371) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 372) hr |>.elim
    · exact dvd_373
    · exact (by decide : ¬ Nat.Prime 374) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 375) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 376) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 377) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 378) hr |>.elim
    · exact dvd_379
    · exact (by decide : ¬ Nat.Prime 380) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 381) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 382) hr |>.elim
    · exact dvd_383
    · exact (by decide : ¬ Nat.Prime 384) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 385) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 386) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 387) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 388) hr |>.elim
    · exact dvd_389
    · exact (by decide : ¬ Nat.Prime 390) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 391) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 392) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 393) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 394) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 395) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 396) hr |>.elim
    · exact dvd_397
    · exact (by decide : ¬ Nat.Prime 398) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 399) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 400) hr |>.elim
    · exact dvd_401
    · exact (by decide : ¬ Nat.Prime 402) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 403) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 404) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 405) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 406) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 407) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 408) hr |>.elim
    · exact dvd_409
    · exact (by decide : ¬ Nat.Prime 410) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 411) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 412) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 413) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 414) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 415) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 416) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 417) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 418) hr |>.elim
    · exact dvd_419
    · exact (by decide : ¬ Nat.Prime 420) hr |>.elim
    · exact dvd_421
    · exact (by decide : ¬ Nat.Prime 422) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 423) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 424) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 425) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 426) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 427) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 428) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 429) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 430) hr |>.elim
    · exact dvd_431
    · exact (by decide : ¬ Nat.Prime 432) hr |>.elim
    · exact dvd_433
    · exact (by decide : ¬ Nat.Prime 434) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 435) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 436) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 437) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 438) hr |>.elim
    · exact dvd_439
    · exact (by decide : ¬ Nat.Prime 440) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 441) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 442) hr |>.elim
    · exact dvd_443
    · exact (by decide : ¬ Nat.Prime 444) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 445) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 446) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 447) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 448) hr |>.elim
    · exact dvd_449
    · exact (by decide : ¬ Nat.Prime 450) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 451) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 452) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 453) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 454) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 455) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 456) hr |>.elim
    · exact dvd_457
    · exact (by decide : ¬ Nat.Prime 458) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 459) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 460) hr |>.elim
    · exact dvd_461
    · exact (by decide : ¬ Nat.Prime 462) hr |>.elim
    · exact dvd_463
    · exact (by decide : ¬ Nat.Prime 464) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 465) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 466) hr |>.elim
    · exact dvd_467
    · exact (by decide : ¬ Nat.Prime 468) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 469) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 470) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 471) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 472) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 473) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 474) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 475) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 476) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 477) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 478) hr |>.elim
    · exact dvd_479
    · exact (by decide : ¬ Nat.Prime 480) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 481) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 482) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 483) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 484) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 485) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 486) hr |>.elim
    · exact dvd_487
    · exact (by decide : ¬ Nat.Prime 488) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 489) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 490) hr |>.elim
    · exact dvd_491
    · exact (by decide : ¬ Nat.Prime 492) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 493) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 494) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 495) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 496) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 497) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 498) hr |>.elim
    · exact dvd_499
    · exact (by decide : ¬ Nat.Prime 500) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 501) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 502) hr |>.elim
    · exact dvd_503
    · exact (by decide : ¬ Nat.Prime 504) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 505) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 506) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 507) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 508) hr |>.elim
    · exact dvd_509

lemma prime_not_dvd_x_seq_509 (p : ℕ) (hp_lt : p < 271443) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
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
            have hr_le : r ≤ 509 := by
              by_contra h_gt
              have hr_ge : r ≥ 510 := by omega
              have hr_lt_521 : r < 521 := by
                by_contra h_ge'
                have : r ≥ 521 := by omega
                have : r^2 ≥ 271441 := by nlinarith
                omega
              interval_cases r
              · exact (by decide : ¬ Nat.Prime 510) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 511) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 512) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 513) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 514) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 515) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 516) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 517) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 518) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 519) hr_prime |>.elim
              · exact (by decide : ¬ Nat.Prime 520) hr_prime |>.elim
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_509 r hr_le hr_prime
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
lemma gcd_521_aux (n : ℕ) (hn : n = 11981) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 11981 (by decide) (by norm_num) (by norm_num)
lemma dvd_521_aux (n : ℕ) (hn : n = 11981) : 521 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 11981 (by decide)
  rw [gcd_521_aux 11981 rfl] at h
  have h_calc : 2 + 11981 / 1 = 11983 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 521 11983 (x_seq (11981 - 1)) (by decide)
lemma dvd_521 : 521 ∣ x_seq (521^2 - 1) := by
  have h_dvd : x_seq 11981 ∣ x_seq (521^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_521_aux 11981 rfl) h_dvd
lemma gcd_523_aux (n : ℕ) (hn : n = 521) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 521 (by decide) (by norm_num) (by norm_num)
lemma dvd_523_aux (n : ℕ) (hn : n = 521) : 523 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 521 (by decide)
  rw [gcd_523_aux 521 rfl] at h
  have h_calc : 2 + 521 / 1 = 523 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 523 523 (x_seq (521 - 1)) (by decide)
lemma dvd_523 : 523 ∣ x_seq (523^2 - 1) := by
  have h_dvd : x_seq 521 ∣ x_seq (523^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_523_aux 521 rfl) h_dvd
lemma gcd_541_aux (n : ℕ) (hn : n = 29753) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 29753 (by decide) (by norm_num) (by norm_num)
lemma dvd_541_aux (n : ℕ) (hn : n = 29753) : 541 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 29753 (by decide)
  rw [gcd_541_aux 29753 rfl] at h
  have h_calc : 2 + 29753 / 1 = 29755 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 541 29755 (x_seq (29753 - 1)) (by decide)
lemma dvd_541 : 541 ∣ x_seq (541^2 - 1) := by
  have h_dvd : x_seq 29753 ∣ x_seq (541^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_541_aux 29753 rfl) h_dvd
lemma gcd_547_aux (n : ℕ) (hn : n = 7109) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7109 (by decide) (by norm_num) (by norm_num)
lemma dvd_547_aux (n : ℕ) (hn : n = 7109) : 547 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7109 (by decide)
  rw [gcd_547_aux 7109 rfl] at h
  have h_calc : 2 + 7109 / 1 = 7111 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 547 7111 (x_seq (7109 - 1)) (by decide)
lemma dvd_547 : 547 ∣ x_seq (547^2 - 1) := by
  have h_dvd : x_seq 7109 ∣ x_seq (547^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_547_aux 7109 rfl) h_dvd
lemma gcd_557_aux (n : ℕ) (hn : n = 18379) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 18379 (by decide) (by norm_num) (by norm_num)
lemma dvd_557_aux (n : ℕ) (hn : n = 18379) : 557 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 18379 (by decide)
  rw [gcd_557_aux 18379 rfl] at h
  have h_calc : 2 + 18379 / 1 = 18381 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 557 18381 (x_seq (18379 - 1)) (by decide)
lemma dvd_557 : 557 ∣ x_seq (557^2 - 1) := by
  have h_dvd : x_seq 18379 ∣ x_seq (557^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_557_aux 18379 rfl) h_dvd
lemma gcd_563_aux (n : ℕ) (hn : n = 8443) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 8443 (by decide) (by norm_num) (by norm_num)
lemma dvd_563_aux (n : ℕ) (hn : n = 8443) : 563 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 8443 (by decide)
  rw [gcd_563_aux 8443 rfl] at h
  have h_calc : 2 + 8443 / 1 = 8445 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 563 8445 (x_seq (8443 - 1)) (by decide)
lemma dvd_563 : 563 ∣ x_seq (563^2 - 1) := by
  have h_dvd : x_seq 8443 ∣ x_seq (563^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_563_aux 8443 rfl) h_dvd
lemma gcd_569_aux (n : ℕ) (hn : n = 5119) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5119 (by decide) (by norm_num) (by norm_num)
lemma dvd_569_aux (n : ℕ) (hn : n = 5119) : 569 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5119 (by decide)
  rw [gcd_569_aux 5119 rfl] at h
  have h_calc : 2 + 5119 / 1 = 5121 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 569 5121 (x_seq (5119 - 1)) (by decide)
lemma dvd_569 : 569 ∣ x_seq (569^2 - 1) := by
  have h_dvd : x_seq 5119 ∣ x_seq (569^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_569_aux 5119 rfl) h_dvd
lemma gcd_571_aux (n : ℕ) (hn : n = 569) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 569 (by decide) (by norm_num) (by norm_num)
lemma dvd_571_aux (n : ℕ) (hn : n = 569) : 571 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 569 (by decide)
  rw [gcd_571_aux 569 rfl] at h
  have h_calc : 2 + 569 / 1 = 571 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 571 571 (x_seq (569 - 1)) (by decide)
lemma dvd_571 : 571 ∣ x_seq (571^2 - 1) := by
  have h_dvd : x_seq 569 ∣ x_seq (571^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_571_aux 569 rfl) h_dvd
lemma gcd_577_aux (n : ℕ) (hn : n = 7499) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7499 (by decide) (by norm_num) (by norm_num)
lemma dvd_577_aux (n : ℕ) (hn : n = 7499) : 577 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7499 (by decide)
  rw [gcd_577_aux 7499 rfl] at h
  have h_calc : 2 + 7499 / 1 = 7501 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 577 7501 (x_seq (7499 - 1)) (by decide)
lemma dvd_577 : 577 ∣ x_seq (577^2 - 1) := by
  have h_dvd : x_seq 7499 ∣ x_seq (577^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_577_aux 7499 rfl) h_dvd
lemma gcd_587_aux (n : ℕ) (hn : n = 1759) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1759 (by decide) (by norm_num) (by norm_num)
lemma dvd_587_aux (n : ℕ) (hn : n = 1759) : 587 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1759 (by decide)
  rw [gcd_587_aux 1759 rfl] at h
  have h_calc : 2 + 1759 / 1 = 1761 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 587 1761 (x_seq (1759 - 1)) (by decide)
lemma dvd_587 : 587 ∣ x_seq (587^2 - 1) := by
  have h_dvd : x_seq 1759 ∣ x_seq (587^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_587_aux 1759 rfl) h_dvd
lemma gcd_593_aux (n : ℕ) (hn : n = 1777) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1777 (by decide) (by norm_num) (by norm_num)
lemma dvd_593_aux (n : ℕ) (hn : n = 1777) : 593 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1777 (by decide)
  rw [gcd_593_aux 1777 rfl] at h
  have h_calc : 2 + 1777 / 1 = 1779 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 593 1779 (x_seq (1777 - 1)) (by decide)
lemma dvd_593 : 593 ∣ x_seq (593^2 - 1) := by
  have h_dvd : x_seq 1777 ∣ x_seq (593^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_593_aux 1777 rfl) h_dvd
lemma gcd_599_aux (n : ℕ) (hn : n = 10181) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 10181 (by decide) (by norm_num) (by norm_num)
lemma dvd_599_aux (n : ℕ) (hn : n = 10181) : 599 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 10181 (by decide)
  rw [gcd_599_aux 10181 rfl] at h
  have h_calc : 2 + 10181 / 1 = 10183 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 599 10183 (x_seq (10181 - 1)) (by decide)
lemma dvd_599 : 599 ∣ x_seq (599^2 - 1) := by
  have h_dvd : x_seq 10181 ∣ x_seq (599^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_599_aux 10181 rfl) h_dvd
lemma gcd_601_aux (n : ℕ) (hn : n = 599) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 599 (by decide) (by norm_num) (by norm_num)
lemma dvd_601_aux (n : ℕ) (hn : n = 599) : 601 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 599 (by decide)
  rw [gcd_601_aux 599 rfl] at h
  have h_calc : 2 + 599 / 1 = 601 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 601 601 (x_seq (599 - 1)) (by decide)
lemma dvd_601 : 601 ∣ x_seq (601^2 - 1) := by
  have h_dvd : x_seq 599 ∣ x_seq (601^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_601_aux 599 rfl) h_dvd
lemma gcd_607_aux (n : ℕ) (hn : n = 9103) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 9103 (by decide) (by norm_num) (by norm_num)
lemma dvd_607_aux (n : ℕ) (hn : n = 9103) : 607 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 9103 (by decide)
  rw [gcd_607_aux 9103 rfl] at h
  have h_calc : 2 + 9103 / 1 = 9105 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 607 9105 (x_seq (9103 - 1)) (by decide)
lemma dvd_607 : 607 ∣ x_seq (607^2 - 1) := by
  have h_dvd : x_seq 9103 ∣ x_seq (607^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_607_aux 9103 rfl) h_dvd
lemma gcd_613_aux (n : ℕ) (hn : n = 26357) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 26357 (by decide) (by norm_num) (by norm_num)
lemma dvd_613_aux (n : ℕ) (hn : n = 26357) : 613 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 26357 (by decide)
  rw [gcd_613_aux 26357 rfl] at h
  have h_calc : 2 + 26357 / 1 = 26359 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 613 26359 (x_seq (26357 - 1)) (by decide)
lemma dvd_613 : 613 ∣ x_seq (613^2 - 1) := by
  have h_dvd : x_seq 26357 ∣ x_seq (613^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_613_aux 26357 rfl) h_dvd
lemma gcd_617_aux (n : ℕ) (hn : n = 3083) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3083 (by decide) (by norm_num) (by norm_num)
lemma dvd_617_aux (n : ℕ) (hn : n = 3083) : 617 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3083 (by decide)
  rw [gcd_617_aux 3083 rfl] at h
  have h_calc : 2 + 3083 / 1 = 3085 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 617 3085 (x_seq (3083 - 1)) (by decide)
lemma dvd_617 : 617 ∣ x_seq (617^2 - 1) := by
  have h_dvd : x_seq 3083 ∣ x_seq (617^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_617_aux 3083 rfl) h_dvd
lemma gcd_619_aux (n : ℕ) (hn : n = 617) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 617 (by decide) (by norm_num) (by norm_num)
lemma dvd_619_aux (n : ℕ) (hn : n = 617) : 619 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 617 (by decide)
  rw [gcd_619_aux 617 rfl] at h
  have h_calc : 2 + 617 / 1 = 619 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 619 619 (x_seq (617 - 1)) (by decide)
lemma dvd_619 : 619 ∣ x_seq (619^2 - 1) := by
  have h_dvd : x_seq 617 ∣ x_seq (619^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_619_aux 617 rfl) h_dvd
lemma gcd_631_aux (n : ℕ) (hn : n = 11987) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 11987 (by decide) (by norm_num) (by norm_num)
lemma dvd_631_aux (n : ℕ) (hn : n = 11987) : 631 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 11987 (by decide)
  rw [gcd_631_aux 11987 rfl] at h
  have h_calc : 2 + 11987 / 1 = 11989 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 631 11989 (x_seq (11987 - 1)) (by decide)
lemma dvd_631 : 631 ∣ x_seq (631^2 - 1) := by
  have h_dvd : x_seq 11987 ∣ x_seq (631^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_631_aux 11987 rfl) h_dvd
lemma gcd_641_aux (n : ℕ) (hn : n = 3203) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3203 (by decide) (by norm_num) (by norm_num)
lemma dvd_641_aux (n : ℕ) (hn : n = 3203) : 641 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3203 (by decide)
  rw [gcd_641_aux 3203 rfl] at h
  have h_calc : 2 + 3203 / 1 = 3205 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 641 3205 (x_seq (3203 - 1)) (by decide)
lemma dvd_641 : 641 ∣ x_seq (641^2 - 1) := by
  have h_dvd : x_seq 3203 ∣ x_seq (641^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_641_aux 3203 rfl) h_dvd
lemma gcd_643_aux (n : ℕ) (hn : n = 641) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 641 (by decide) (by norm_num) (by norm_num)
lemma dvd_643_aux (n : ℕ) (hn : n = 641) : 643 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 641 (by decide)
  rw [gcd_643_aux 641 rfl] at h
  have h_calc : 2 + 641 / 1 = 643 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 643 643 (x_seq (641 - 1)) (by decide)
lemma dvd_643 : 643 ∣ x_seq (643^2 - 1) := by
  have h_dvd : x_seq 641 ∣ x_seq (643^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_643_aux 641 rfl) h_dvd
lemma gcd_647_aux (n : ℕ) (hn : n = 5821) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5821 (by decide) (by norm_num) (by norm_num)
lemma dvd_647_aux (n : ℕ) (hn : n = 5821) : 647 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5821 (by decide)
  rw [gcd_647_aux 5821 rfl] at h
  have h_calc : 2 + 5821 / 1 = 5823 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 647 5823 (x_seq (5821 - 1)) (by decide)
lemma dvd_647 : 647 ∣ x_seq (647^2 - 1) := by
  have h_dvd : x_seq 5821 ∣ x_seq (647^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_647_aux 5821 rfl) h_dvd
lemma gcd_653_aux (n : ℕ) (hn : n = 15017) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 15017 (by decide) (by norm_num) (by norm_num)
lemma dvd_653_aux (n : ℕ) (hn : n = 15017) : 653 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 15017 (by decide)
  rw [gcd_653_aux 15017 rfl] at h
  have h_calc : 2 + 15017 / 1 = 15019 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 653 15019 (x_seq (15017 - 1)) (by decide)
lemma dvd_653 : 653 ∣ x_seq (653^2 - 1) := by
  have h_dvd : x_seq 15017 ∣ x_seq (653^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_653_aux 15017 rfl) h_dvd
lemma gcd_659_aux (n : ℕ) (hn : n = 7247) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7247 (by decide) (by norm_num) (by norm_num)
lemma dvd_659_aux (n : ℕ) (hn : n = 7247) : 659 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7247 (by decide)
  rw [gcd_659_aux 7247 rfl] at h
  have h_calc : 2 + 7247 / 1 = 7249 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 659 7249 (x_seq (7247 - 1)) (by decide)
lemma dvd_659 : 659 ∣ x_seq (659^2 - 1) := by
  have h_dvd : x_seq 7247 ∣ x_seq (659^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_659_aux 7247 rfl) h_dvd
lemma gcd_661_aux (n : ℕ) (hn : n = 659) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 659 (by decide) (by norm_num) (by norm_num)
lemma dvd_661_aux (n : ℕ) (hn : n = 659) : 661 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 659 (by decide)
  rw [gcd_661_aux 659 rfl] at h
  have h_calc : 2 + 659 / 1 = 661 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 661 661 (x_seq (659 - 1)) (by decide)
lemma dvd_661 : 661 ∣ x_seq (661^2 - 1) := by
  have h_dvd : x_seq 659 ∣ x_seq (661^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_661_aux 659 rfl) h_dvd
lemma gcd_673_aux (n : ℕ) (hn : n = 2017) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2017 (by decide) (by norm_num) (by norm_num)
lemma dvd_673_aux (n : ℕ) (hn : n = 2017) : 673 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2017 (by decide)
  rw [gcd_673_aux 2017 rfl] at h
  have h_calc : 2 + 2017 / 1 = 2019 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 673 2019 (x_seq (2017 - 1)) (by decide)
lemma dvd_673 : 673 ∣ x_seq (673^2 - 1) := by
  have h_dvd : x_seq 2017 ∣ x_seq (673^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_673_aux 2017 rfl) h_dvd
lemma gcd_677_aux (n : ℕ) (hn : n = 31817) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 31817 (by decide) (by norm_num) (by norm_num)
lemma dvd_677_aux (n : ℕ) (hn : n = 31817) : 677 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 31817 (by decide)
  rw [gcd_677_aux 31817 rfl] at h
  have h_calc : 2 + 31817 / 1 = 31819 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 677 31819 (x_seq (31817 - 1)) (by decide)
lemma dvd_677 : 677 ∣ x_seq (677^2 - 1) := by
  have h_dvd : x_seq 31817 ∣ x_seq (677^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_677_aux 31817 rfl) h_dvd
lemma gcd_683_aux (n : ℕ) (hn : n = 3413) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3413 (by decide) (by norm_num) (by norm_num)
lemma dvd_683_aux (n : ℕ) (hn : n = 3413) : 683 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3413 (by decide)
  rw [gcd_683_aux 3413 rfl] at h
  have h_calc : 2 + 3413 / 1 = 3415 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 683 3415 (x_seq (3413 - 1)) (by decide)
lemma dvd_683 : 683 ∣ x_seq (683^2 - 1) := by
  have h_dvd : x_seq 3413 ∣ x_seq (683^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_683_aux 3413 rfl) h_dvd
lemma gcd_691_aux (n : ℕ) (hn : n = 6217) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 6217 (by decide) (by norm_num) (by norm_num)
lemma dvd_691_aux (n : ℕ) (hn : n = 6217) : 691 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6217 (by decide)
  rw [gcd_691_aux 6217 rfl] at h
  have h_calc : 2 + 6217 / 1 = 6219 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 691 6219 (x_seq (6217 - 1)) (by decide)
lemma dvd_691 : 691 ∣ x_seq (691^2 - 1) := by
  have h_dvd : x_seq 6217 ∣ x_seq (691^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_691_aux 6217 rfl) h_dvd
lemma gcd_701_aux (n : ℕ) (hn : n = 10513) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 10513 (by decide) (by norm_num) (by norm_num)
lemma dvd_701_aux (n : ℕ) (hn : n = 10513) : 701 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 10513 (by decide)
  rw [gcd_701_aux 10513 rfl] at h
  have h_calc : 2 + 10513 / 1 = 10515 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 701 10515 (x_seq (10513 - 1)) (by decide)
lemma dvd_701 : 701 ∣ x_seq (701^2 - 1) := by
  have h_dvd : x_seq 10513 ∣ x_seq (701^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_701_aux 10513 rfl) h_dvd
lemma gcd_709_aux (n : ℕ) (hn : n = 13469) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 13469 (by decide) (by norm_num) (by norm_num)
lemma dvd_709_aux (n : ℕ) (hn : n = 13469) : 709 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 13469 (by decide)
  rw [gcd_709_aux 13469 rfl] at h
  have h_calc : 2 + 13469 / 1 = 13471 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 709 13471 (x_seq (13469 - 1)) (by decide)
lemma dvd_709 : 709 ∣ x_seq (709^2 - 1) := by
  have h_dvd : x_seq 13469 ∣ x_seq (709^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_709_aux 13469 rfl) h_dvd
lemma gcd_719_aux (n : ℕ) (hn : n = 3593) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3593 (by decide) (by norm_num) (by norm_num)
lemma dvd_719_aux (n : ℕ) (hn : n = 3593) : 719 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3593 (by decide)
  rw [gcd_719_aux 3593 rfl] at h
  have h_calc : 2 + 3593 / 1 = 3595 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 719 3595 (x_seq (3593 - 1)) (by decide)
lemma dvd_719 : 719 ∣ x_seq (719^2 - 1) := by
  have h_dvd : x_seq 3593 ∣ x_seq (719^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_719_aux 3593 rfl) h_dvd
lemma gcd_727_aux (n : ℕ) (hn : n = 2179) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2179 (by decide) (by norm_num) (by norm_num)
lemma dvd_727_aux (n : ℕ) (hn : n = 2179) : 727 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2179 (by decide)
  rw [gcd_727_aux 2179 rfl] at h
  have h_calc : 2 + 2179 / 1 = 2181 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 727 2181 (x_seq (2179 - 1)) (by decide)
lemma dvd_727 : 727 ∣ x_seq (727^2 - 1) := by
  have h_dvd : x_seq 2179 ∣ x_seq (727^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_727_aux 2179 rfl) h_dvd
lemma gcd_733_aux (n : ℕ) (hn : n = 10993) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 10993 (by decide) (by norm_num) (by norm_num)
lemma dvd_733_aux (n : ℕ) (hn : n = 10993) : 733 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 10993 (by decide)
  rw [gcd_733_aux 10993 rfl] at h
  have h_calc : 2 + 10993 / 1 = 10995 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 733 10995 (x_seq (10993 - 1)) (by decide)
lemma dvd_733 : 733 ∣ x_seq (733^2 - 1) := by
  have h_dvd : x_seq 10993 ∣ x_seq (733^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_733_aux 10993 rfl) h_dvd
lemma gcd_739_aux (n : ℕ) (hn : n = 22907) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 22907 (by decide) (by norm_num) (by norm_num)
lemma dvd_739_aux (n : ℕ) (hn : n = 22907) : 739 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 22907 (by decide)
  rw [gcd_739_aux 22907 rfl] at h
  have h_calc : 2 + 22907 / 1 = 22909 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 739 22909 (x_seq (22907 - 1)) (by decide)
lemma dvd_739 : 739 ∣ x_seq (739^2 - 1) := by
  have h_dvd : x_seq 22907 ∣ x_seq (739^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_739_aux 22907 rfl) h_dvd
lemma gcd_743_aux (n : ℕ) (hn : n = 8171) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 8171 (by decide) (by norm_num) (by norm_num)
lemma dvd_743_aux (n : ℕ) (hn : n = 8171) : 743 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 8171 (by decide)
  rw [gcd_743_aux 8171 rfl] at h
  have h_calc : 2 + 8171 / 1 = 8173 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 743 8173 (x_seq (8171 - 1)) (by decide)
lemma dvd_743 : 743 ∣ x_seq (743^2 - 1) := by
  have h_dvd : x_seq 8171 ∣ x_seq (743^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_743_aux 8171 rfl) h_dvd
lemma gcd_751_aux (n : ℕ) (hn : n = 2251) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2251 (by decide) (by norm_num) (by norm_num)
lemma dvd_751_aux (n : ℕ) (hn : n = 2251) : 751 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2251 (by decide)
  rw [gcd_751_aux 2251 rfl] at h
  have h_calc : 2 + 2251 / 1 = 2253 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 751 2253 (x_seq (2251 - 1)) (by decide)
lemma dvd_751 : 751 ∣ x_seq (751^2 - 1) := by
  have h_dvd : x_seq 2251 ∣ x_seq (751^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_751_aux 2251 rfl) h_dvd
lemma gcd_757_aux (n : ℕ) (hn : n = 5297) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5297 (by decide) (by norm_num) (by norm_num)
lemma dvd_757_aux (n : ℕ) (hn : n = 5297) : 757 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5297 (by decide)
  rw [gcd_757_aux 5297 rfl] at h
  have h_calc : 2 + 5297 / 1 = 5299 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 757 5299 (x_seq (5297 - 1)) (by decide)
lemma dvd_757 : 757 ∣ x_seq (757^2 - 1) := by
  have h_dvd : x_seq 5297 ∣ x_seq (757^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_757_aux 5297 rfl) h_dvd
lemma gcd_761_aux (n : ℕ) (hn : n = 2281) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2281 (by decide) (by norm_num) (by norm_num)
lemma dvd_761_aux (n : ℕ) (hn : n = 2281) : 761 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2281 (by decide)
  rw [gcd_761_aux 2281 rfl] at h
  have h_calc : 2 + 2281 / 1 = 2283 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 761 2283 (x_seq (2281 - 1)) (by decide)
lemma dvd_761 : 761 ∣ x_seq (761^2 - 1) := by
  have h_dvd : x_seq 2281 ∣ x_seq (761^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_761_aux 2281 rfl) h_dvd
lemma gcd_769_aux (n : ℕ) (hn : n = 5381) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5381 (by decide) (by norm_num) (by norm_num)
lemma dvd_769_aux (n : ℕ) (hn : n = 5381) : 769 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5381 (by decide)
  rw [gcd_769_aux 5381 rfl] at h
  have h_calc : 2 + 5381 / 1 = 5383 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 769 5383 (x_seq (5381 - 1)) (by decide)
lemma dvd_769 : 769 ∣ x_seq (769^2 - 1) := by
  have h_dvd : x_seq 5381 ∣ x_seq (769^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_769_aux 5381 rfl) h_dvd
lemma gcd_773_aux (n : ℕ) (hn : n = 3863) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3863 (by decide) (by norm_num) (by norm_num)
lemma dvd_773_aux (n : ℕ) (hn : n = 3863) : 773 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3863 (by decide)
  rw [gcd_773_aux 3863 rfl] at h
  have h_calc : 2 + 3863 / 1 = 3865 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 773 3865 (x_seq (3863 - 1)) (by decide)
lemma dvd_773 : 773 ∣ x_seq (773^2 - 1) := by
  have h_dvd : x_seq 3863 ∣ x_seq (773^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_773_aux 3863 rfl) h_dvd
lemma gcd_787_aux (n : ℕ) (hn : n = 5507) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5507 (by decide) (by norm_num) (by norm_num)
lemma dvd_787_aux (n : ℕ) (hn : n = 5507) : 787 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5507 (by decide)
  rw [gcd_787_aux 5507 rfl] at h
  have h_calc : 2 + 5507 / 1 = 5509 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 787 5509 (x_seq (5507 - 1)) (by decide)
lemma dvd_787 : 787 ∣ x_seq (787^2 - 1) := by
  have h_dvd : x_seq 5507 ∣ x_seq (787^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_787_aux 5507 rfl) h_dvd
lemma gcd_797_aux (n : ℕ) (hn : n = 2389) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2389 (by decide) (by norm_num) (by norm_num)
lemma dvd_797_aux (n : ℕ) (hn : n = 2389) : 797 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2389 (by decide)
  rw [gcd_797_aux 2389 rfl] at h
  have h_calc : 2 + 2389 / 1 = 2391 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 797 2391 (x_seq (2389 - 1)) (by decide)
lemma dvd_797 : 797 ∣ x_seq (797^2 - 1) := by
  have h_dvd : x_seq 2389 ∣ x_seq (797^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_797_aux 2389 rfl) h_dvd
lemma gcd_809_aux (n : ℕ) (hn : n = 16987) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 16987 (by decide) (by norm_num) (by norm_num)
lemma dvd_809_aux (n : ℕ) (hn : n = 16987) : 809 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 16987 (by decide)
  rw [gcd_809_aux 16987 rfl] at h
  have h_calc : 2 + 16987 / 1 = 16989 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 809 16989 (x_seq (16987 - 1)) (by decide)
lemma dvd_809 : 809 ∣ x_seq (809^2 - 1) := by
  have h_dvd : x_seq 16987 ∣ x_seq (809^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_809_aux 16987 rfl) h_dvd
lemma gcd_811_aux (n : ℕ) (hn : n = 809) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 809 (by decide) (by norm_num) (by norm_num)
lemma dvd_811_aux (n : ℕ) (hn : n = 809) : 811 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 809 (by decide)
  rw [gcd_811_aux 809 rfl] at h
  have h_calc : 2 + 809 / 1 = 811 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 811 811 (x_seq (809 - 1)) (by decide)
lemma dvd_811 : 811 ∣ x_seq (811^2 - 1) := by
  have h_dvd : x_seq 809 ∣ x_seq (811^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_811_aux 809 rfl) h_dvd
lemma gcd_821_aux (n : ℕ) (hn : n = 9029) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 9029 (by decide) (by norm_num) (by norm_num)
lemma dvd_821_aux (n : ℕ) (hn : n = 9029) : 821 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 9029 (by decide)
  rw [gcd_821_aux 9029 rfl] at h
  have h_calc : 2 + 9029 / 1 = 9031 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 821 9031 (x_seq (9029 - 1)) (by decide)
lemma dvd_821 : 821 ∣ x_seq (821^2 - 1) := by
  have h_dvd : x_seq 9029 ∣ x_seq (821^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_821_aux 9029 rfl) h_dvd
lemma gcd_823_aux (n : ℕ) (hn : n = 821) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 821 (by decide) (by norm_num) (by norm_num)
lemma dvd_823_aux (n : ℕ) (hn : n = 821) : 823 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 821 (by decide)
  rw [gcd_823_aux 821 rfl] at h
  have h_calc : 2 + 821 / 1 = 823 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 823 823 (x_seq (821 - 1)) (by decide)
lemma dvd_823 : 823 ∣ x_seq (823^2 - 1) := by
  have h_dvd : x_seq 821 ∣ x_seq (823^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_823_aux 821 rfl) h_dvd
lemma gcd_827_aux (n : ℕ) (hn : n = 4133) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 4133 (by decide) (by norm_num) (by norm_num)
lemma dvd_827_aux (n : ℕ) (hn : n = 4133) : 827 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 4133 (by decide)
  rw [gcd_827_aux 4133 rfl] at h
  have h_calc : 2 + 4133 / 1 = 4135 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 827 4135 (x_seq (4133 - 1)) (by decide)
lemma dvd_827 : 827 ∣ x_seq (827^2 - 1) := by
  have h_dvd : x_seq 4133 ∣ x_seq (827^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_827_aux 4133 rfl) h_dvd
lemma gcd_829_aux (n : ℕ) (hn : n = 827) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 827 (by decide) (by norm_num) (by norm_num)
lemma dvd_829_aux (n : ℕ) (hn : n = 827) : 829 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 827 (by decide)
  rw [gcd_829_aux 827 rfl] at h
  have h_calc : 2 + 827 / 1 = 829 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 829 829 (x_seq (827 - 1)) (by decide)
lemma dvd_829 : 829 ∣ x_seq (829^2 - 1) := by
  have h_dvd : x_seq 827 ∣ x_seq (829^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_829_aux 827 rfl) h_dvd
lemma gcd_839_aux (n : ℕ) (hn : n = 9227) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 9227 (by decide) (by norm_num) (by norm_num)
lemma dvd_839_aux (n : ℕ) (hn : n = 9227) : 839 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 9227 (by decide)
  rw [gcd_839_aux 9227 rfl] at h
  have h_calc : 2 + 9227 / 1 = 9229 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 839 9229 (x_seq (9227 - 1)) (by decide)
lemma dvd_839 : 839 ∣ x_seq (839^2 - 1) := by
  have h_dvd : x_seq 9227 ∣ x_seq (839^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_839_aux 9227 rfl) h_dvd
lemma gcd_853_aux (n : ℕ) (hn : n = 2557) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2557 (by decide) (by norm_num) (by norm_num)
lemma dvd_853_aux (n : ℕ) (hn : n = 2557) : 853 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2557 (by decide)
  rw [gcd_853_aux 2557 rfl] at h
  have h_calc : 2 + 2557 / 1 = 2559 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 853 2559 (x_seq (2557 - 1)) (by decide)
lemma dvd_853 : 853 ∣ x_seq (853^2 - 1) := by
  have h_dvd : x_seq 2557 ∣ x_seq (853^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_853_aux 2557 rfl) h_dvd
lemma gcd_857_aux (n : ℕ) (hn : n = 12853) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 12853 (by decide) (by norm_num) (by norm_num)
lemma dvd_857_aux (n : ℕ) (hn : n = 12853) : 857 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 12853 (by decide)
  rw [gcd_857_aux 12853 rfl] at h
  have h_calc : 2 + 12853 / 1 = 12855 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 857 12855 (x_seq (12853 - 1)) (by decide)
lemma dvd_857 : 857 ∣ x_seq (857^2 - 1) := by
  have h_dvd : x_seq 12853 ∣ x_seq (857^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_857_aux 12853 rfl) h_dvd
lemma gcd_859_aux (n : ℕ) (hn : n = 857) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 857 (by decide) (by norm_num) (by norm_num)
lemma dvd_859_aux (n : ℕ) (hn : n = 857) : 859 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 857 (by decide)
  rw [gcd_859_aux 857 rfl] at h
  have h_calc : 2 + 857 / 1 = 859 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 859 859 (x_seq (857 - 1)) (by decide)
lemma dvd_859 : 859 ∣ x_seq (859^2 - 1) := by
  have h_dvd : x_seq 857 ∣ x_seq (859^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_859_aux 857 rfl) h_dvd
lemma gcd_863_aux (n : ℕ) (hn : n = 28477) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 28477 (by decide) (by norm_num) (by norm_num)
lemma dvd_863_aux (n : ℕ) (hn : n = 28477) : 863 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 28477 (by decide)
  rw [gcd_863_aux 28477 rfl] at h
  have h_calc : 2 + 28477 / 1 = 28479 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 863 28479 (x_seq (28477 - 1)) (by decide)
lemma dvd_863 : 863 ∣ x_seq (863^2 - 1) := by
  have h_dvd : x_seq 28477 ∣ x_seq (863^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_863_aux 28477 rfl) h_dvd
lemma gcd_877_aux (n : ℕ) (hn : n = 11399) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 11399 (by decide) (by norm_num) (by norm_num)
lemma dvd_877_aux (n : ℕ) (hn : n = 11399) : 877 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 11399 (by decide)
  rw [gcd_877_aux 11399 rfl] at h
  have h_calc : 2 + 11399 / 1 = 11401 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 877 11401 (x_seq (11399 - 1)) (by decide)
lemma dvd_877 : 877 ∣ x_seq (877^2 - 1) := by
  have h_dvd : x_seq 11399 ∣ x_seq (877^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_877_aux 11399 rfl) h_dvd
lemma gcd_881_aux (n : ℕ) (hn : n = 7927) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7927 (by decide) (by norm_num) (by norm_num)
lemma dvd_881_aux (n : ℕ) (hn : n = 7927) : 881 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7927 (by decide)
  rw [gcd_881_aux 7927 rfl] at h
  have h_calc : 2 + 7927 / 1 = 7929 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 881 7929 (x_seq (7927 - 1)) (by decide)
lemma dvd_881 : 881 ∣ x_seq (881^2 - 1) := by
  have h_dvd : x_seq 7927 ∣ x_seq (881^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_881_aux 7927 rfl) h_dvd
lemma gcd_883_aux (n : ℕ) (hn : n = 881) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 881 (by decide) (by norm_num) (by norm_num)
lemma dvd_883_aux (n : ℕ) (hn : n = 881) : 883 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 881 (by decide)
  rw [gcd_883_aux 881 rfl] at h
  have h_calc : 2 + 881 / 1 = 883 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 883 883 (x_seq (881 - 1)) (by decide)
lemma dvd_883 : 883 ∣ x_seq (883^2 - 1) := by
  have h_dvd : x_seq 881 ∣ x_seq (883^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_883_aux 881 rfl) h_dvd
lemma gcd_887_aux (n : ℕ) (hn : n = 15077) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 15077 (by decide) (by norm_num) (by norm_num)
lemma dvd_887_aux (n : ℕ) (hn : n = 15077) : 887 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 15077 (by decide)
  rw [gcd_887_aux 15077 rfl] at h
  have h_calc : 2 + 15077 / 1 = 15079 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 887 15079 (x_seq (15077 - 1)) (by decide)
lemma dvd_887 : 887 ∣ x_seq (887^2 - 1) := by
  have h_dvd : x_seq 15077 ∣ x_seq (887^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_887_aux 15077 rfl) h_dvd
lemma gcd_907_aux (n : ℕ) (hn : n = 2719) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 2719 (by decide) (by norm_num) (by norm_num)
lemma dvd_907_aux (n : ℕ) (hn : n = 2719) : 907 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 2719 (by decide)
  rw [gcd_907_aux 2719 rfl] at h
  have h_calc : 2 + 2719 / 1 = 2721 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 907 2721 (x_seq (2719 - 1)) (by decide)
lemma dvd_907 : 907 ∣ x_seq (907^2 - 1) := by
  have h_dvd : x_seq 2719 ∣ x_seq (907^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_907_aux 2719 rfl) h_dvd
lemma gcd_911_aux (n : ℕ) (hn : n = 35527) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 35527 (by decide) (by norm_num) (by norm_num)
lemma dvd_911_aux (n : ℕ) (hn : n = 35527) : 911 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 35527 (by decide)
  rw [gcd_911_aux 35527 rfl] at h
  have h_calc : 2 + 35527 / 1 = 35529 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 911 35529 (x_seq (35527 - 1)) (by decide)
lemma dvd_911 : 911 ∣ x_seq (911^2 - 1) := by
  have h_dvd : x_seq 35527 ∣ x_seq (911^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_911_aux 35527 rfl) h_dvd
lemma gcd_919_aux (n : ℕ) (hn : n = 22973) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 22973 (by decide) (by norm_num) (by norm_num)
lemma dvd_919_aux (n : ℕ) (hn : n = 22973) : 919 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 22973 (by decide)
  rw [gcd_919_aux 22973 rfl] at h
  have h_calc : 2 + 22973 / 1 = 22975 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 919 22975 (x_seq (22973 - 1)) (by decide)
lemma dvd_919 : 919 ∣ x_seq (919^2 - 1) := by
  have h_dvd : x_seq 22973 ∣ x_seq (919^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_919_aux 22973 rfl) h_dvd
lemma gcd_929_aux (n : ℕ) (hn : n = 4643) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 4643 (by decide) (by norm_num) (by norm_num)
lemma dvd_929_aux (n : ℕ) (hn : n = 4643) : 929 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 4643 (by decide)
  rw [gcd_929_aux 4643 rfl] at h
  have h_calc : 2 + 4643 / 1 = 4645 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 929 4645 (x_seq (4643 - 1)) (by decide)
lemma dvd_929 : 929 ∣ x_seq (929^2 - 1) := by
  have h_dvd : x_seq 4643 ∣ x_seq (929^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_929_aux 4643 rfl) h_dvd
lemma gcd_937_aux (n : ℕ) (hn : n = 81517) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 81517 (by decide) (by norm_num) (by norm_num)
lemma dvd_937_aux (n : ℕ) (hn : n = 81517) : 937 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 81517 (by decide)
  rw [gcd_937_aux 81517 rfl] at h
  have h_calc : 2 + 81517 / 1 = 81519 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 937 81519 (x_seq (81517 - 1)) (by decide)
lemma dvd_937 : 937 ∣ x_seq (937^2 - 1) := by
  have h_dvd : x_seq 81517 ∣ x_seq (937^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_937_aux 81517 rfl) h_dvd
lemma gcd_941_aux (n : ℕ) (hn : n = 31051) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 31051 (by decide) (by norm_num) (by norm_num)
lemma dvd_941_aux (n : ℕ) (hn : n = 31051) : 941 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 31051 (by decide)
  rw [gcd_941_aux 31051 rfl] at h
  have h_calc : 2 + 31051 / 1 = 31053 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 941 31053 (x_seq (31051 - 1)) (by decide)
lemma dvd_941 : 941 ∣ x_seq (941^2 - 1) := by
  have h_dvd : x_seq 31051 ∣ x_seq (941^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_941_aux 31051 rfl) h_dvd
lemma gcd_947_aux (n : ℕ) (hn : n = 4733) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 4733 (by decide) (by norm_num) (by norm_num)
lemma dvd_947_aux (n : ℕ) (hn : n = 4733) : 947 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 4733 (by decide)
  rw [gcd_947_aux 4733 rfl] at h
  have h_calc : 2 + 4733 / 1 = 4735 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 947 4735 (x_seq (4733 - 1)) (by decide)
lemma dvd_947 : 947 ∣ x_seq (947^2 - 1) := by
  have h_dvd : x_seq 4733 ∣ x_seq (947^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_947_aux 4733 rfl) h_dvd
lemma gcd_953_aux (n : ℕ) (hn : n = 14293) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 14293 (by decide) (by norm_num) (by norm_num)
lemma dvd_953_aux (n : ℕ) (hn : n = 14293) : 953 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 14293 (by decide)
  rw [gcd_953_aux 14293 rfl] at h
  have h_calc : 2 + 14293 / 1 = 14295 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 953 14295 (x_seq (14293 - 1)) (by decide)
lemma dvd_953 : 953 ∣ x_seq (953^2 - 1) := by
  have h_dvd : x_seq 14293 ∣ x_seq (953^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_953_aux 14293 rfl) h_dvd
lemma gcd_967_aux (n : ℕ) (hn : n = 12569) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 12569 (by decide) (by norm_num) (by norm_num)
lemma dvd_967_aux (n : ℕ) (hn : n = 12569) : 967 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 12569 (by decide)
  rw [gcd_967_aux 12569 rfl] at h
  have h_calc : 2 + 12569 / 1 = 12571 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 967 12571 (x_seq (12569 - 1)) (by decide)
lemma dvd_967 : 967 ∣ x_seq (967^2 - 1) := by
  have h_dvd : x_seq 12569 ∣ x_seq (967^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_967_aux 12569 rfl) h_dvd
lemma gcd_971_aux (n : ℕ) (hn : n = 20389) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 20389 (by decide) (by norm_num) (by norm_num)
lemma dvd_971_aux (n : ℕ) (hn : n = 20389) : 971 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 20389 (by decide)
  rw [gcd_971_aux 20389 rfl] at h
  have h_calc : 2 + 20389 / 1 = 20391 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 971 20391 (x_seq (20389 - 1)) (by decide)
lemma dvd_971 : 971 ∣ x_seq (971^2 - 1) := by
  have h_dvd : x_seq 20389 ∣ x_seq (971^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_971_aux 20389 rfl) h_dvd
lemma gcd_977_aux (n : ℕ) (hn : n = 14653) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 14653 (by decide) (by norm_num) (by norm_num)
lemma dvd_977_aux (n : ℕ) (hn : n = 14653) : 977 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 14653 (by decide)
  rw [gcd_977_aux 14653 rfl] at h
  have h_calc : 2 + 14653 / 1 = 14655 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 977 14655 (x_seq (14653 - 1)) (by decide)
lemma dvd_977 : 977 ∣ x_seq (977^2 - 1) := by
  have h_dvd : x_seq 14653 ∣ x_seq (977^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_977_aux 14653 rfl) h_dvd
lemma gcd_983_aux (n : ℕ) (hn : n = 26539) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 26539 (by decide) (by norm_num) (by norm_num)
lemma dvd_983_aux (n : ℕ) (hn : n = 26539) : 983 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 26539 (by decide)
  rw [gcd_983_aux 26539 rfl] at h
  have h_calc : 2 + 26539 / 1 = 26541 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 983 26541 (x_seq (26539 - 1)) (by decide)
lemma dvd_983 : 983 ∣ x_seq (983^2 - 1) := by
  have h_dvd : x_seq 26539 ∣ x_seq (983^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_983_aux 26539 rfl) h_dvd
lemma gcd_991_aux (n : ℕ) (hn : n = 54503) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 54503 (by decide) (by norm_num) (by norm_num)
lemma dvd_991_aux (n : ℕ) (hn : n = 54503) : 991 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 54503 (by decide)
  rw [gcd_991_aux 54503 rfl] at h
  have h_calc : 2 + 54503 / 1 = 54505 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 991 54505 (x_seq (54503 - 1)) (by decide)
lemma dvd_991 : 991 ∣ x_seq (991^2 - 1) := by
  have h_dvd : x_seq 54503 ∣ x_seq (991^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_991_aux 54503 rfl) h_dvd
lemma gcd_997_aux (n : ℕ) (hn : n = 6977) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 6977 (by decide) (by norm_num) (by norm_num)
lemma dvd_997_aux (n : ℕ) (hn : n = 6977) : 997 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 6977 (by decide)
  rw [gcd_997_aux 6977 rfl] at h
  have h_calc : 2 + 6977 / 1 = 6979 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 997 6979 (x_seq (6977 - 1)) (by decide)
lemma dvd_997 : 997 ∣ x_seq (997^2 - 1) := by
  have h_dvd : x_seq 6977 ∣ x_seq (997^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_997_aux 6977 rfl) h_dvd
lemma gcd_1009_aux (n : ℕ) (hn : n = 21187) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 21187 (by decide) (by norm_num) (by norm_num)
lemma dvd_1009_aux (n : ℕ) (hn : n = 21187) : 1009 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 21187 (by decide)
  rw [gcd_1009_aux 21187 rfl] at h
  have h_calc : 2 + 21187 / 1 = 21189 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1009 21189 (x_seq (21187 - 1)) (by decide)
lemma dvd_1009 : 1009 ∣ x_seq (1009^2 - 1) := by
  have h_dvd : x_seq 21187 ∣ x_seq (1009^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1009_aux 21187 rfl) h_dvd
lemma gcd_1013_aux (n : ℕ) (hn : n = 33427) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 33427 (by decide) (by norm_num) (by norm_num)
lemma dvd_1013_aux (n : ℕ) (hn : n = 33427) : 1013 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 33427 (by decide)
  rw [gcd_1013_aux 33427 rfl] at h
  have h_calc : 2 + 33427 / 1 = 33429 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1013 33429 (x_seq (33427 - 1)) (by decide)
lemma dvd_1013 : 1013 ∣ x_seq (1013^2 - 1) := by
  have h_dvd : x_seq 33427 ∣ x_seq (1013^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1013_aux 33427 rfl) h_dvd
lemma gcd_1019_aux (n : ℕ) (hn : n = 17321) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 17321 (by decide) (by norm_num) (by norm_num)
lemma dvd_1019_aux (n : ℕ) (hn : n = 17321) : 1019 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 17321 (by decide)
  rw [gcd_1019_aux 17321 rfl] at h
  have h_calc : 2 + 17321 / 1 = 17323 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1019 17323 (x_seq (17321 - 1)) (by decide)
lemma dvd_1019 : 1019 ∣ x_seq (1019^2 - 1) := by
  have h_dvd : x_seq 17321 ∣ x_seq (1019^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1019_aux 17321 rfl) h_dvd
lemma gcd_1021_aux (n : ℕ) (hn : n = 1019) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1019 (by decide) (by norm_num) (by norm_num)
lemma dvd_1021_aux (n : ℕ) (hn : n = 1019) : 1021 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1019 (by decide)
  rw [gcd_1021_aux 1019 rfl] at h
  have h_calc : 2 + 1019 / 1 = 1021 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1021 1021 (x_seq (1019 - 1)) (by decide)
lemma dvd_1021 : 1021 ∣ x_seq (1021^2 - 1) := by
  have h_dvd : x_seq 1019 ∣ x_seq (1021^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1021_aux 1019 rfl) h_dvd
lemma gcd_1031_aux (n : ℕ) (hn : n = 5153) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5153 (by decide) (by norm_num) (by norm_num)
lemma dvd_1031_aux (n : ℕ) (hn : n = 5153) : 1031 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5153 (by decide)
  rw [gcd_1031_aux 5153 rfl] at h
  have h_calc : 2 + 5153 / 1 = 5155 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1031 5155 (x_seq (5153 - 1)) (by decide)
lemma dvd_1031 : 1031 ∣ x_seq (1031^2 - 1) := by
  have h_dvd : x_seq 5153 ∣ x_seq (1031^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1031_aux 5153 rfl) h_dvd
lemma gcd_1033_aux (n : ℕ) (hn : n = 1031) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1031 (by decide) (by norm_num) (by norm_num)
lemma dvd_1033_aux (n : ℕ) (hn : n = 1031) : 1033 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1031 (by decide)
  rw [gcd_1033_aux 1031 rfl] at h
  have h_calc : 2 + 1031 / 1 = 1033 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1033 1033 (x_seq (1031 - 1)) (by decide)
lemma dvd_1033 : 1033 ∣ x_seq (1033^2 - 1) := by
  have h_dvd : x_seq 1031 ∣ x_seq (1033^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1033_aux 1031 rfl) h_dvd
lemma gcd_1039_aux (n : ℕ) (hn : n = 19739) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 19739 (by decide) (by norm_num) (by norm_num)
lemma dvd_1039_aux (n : ℕ) (hn : n = 19739) : 1039 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 19739 (by decide)
  rw [gcd_1039_aux 19739 rfl] at h
  have h_calc : 2 + 19739 / 1 = 19741 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1039 19741 (x_seq (19739 - 1)) (by decide)
lemma dvd_1039 : 1039 ∣ x_seq (1039^2 - 1) := by
  have h_dvd : x_seq 19739 ∣ x_seq (1039^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1039_aux 19739 rfl) h_dvd
lemma gcd_1049_aux (n : ℕ) (hn : n = 72379) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 72379 (by decide) (by norm_num) (by norm_num)
lemma dvd_1049_aux (n : ℕ) (hn : n = 72379) : 1049 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 72379 (by decide)
  rw [gcd_1049_aux 72379 rfl] at h
  have h_calc : 2 + 72379 / 1 = 72381 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1049 72381 (x_seq (72379 - 1)) (by decide)
lemma dvd_1049 : 1049 ∣ x_seq (1049^2 - 1) := by
  have h_dvd : x_seq 72379 ∣ x_seq (1049^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1049_aux 72379 rfl) h_dvd
lemma gcd_1051_aux (n : ℕ) (hn : n = 1049) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1049 (by decide) (by norm_num) (by norm_num)
lemma dvd_1051_aux (n : ℕ) (hn : n = 1049) : 1051 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1049 (by decide)
  rw [gcd_1051_aux 1049 rfl] at h
  have h_calc : 2 + 1049 / 1 = 1051 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1051 1051 (x_seq (1049 - 1)) (by decide)
lemma dvd_1051 : 1051 ∣ x_seq (1051^2 - 1) := by
  have h_dvd : x_seq 1049 ∣ x_seq (1051^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1051_aux 1049 rfl) h_dvd
lemma gcd_1061_aux (n : ℕ) (hn : n = 3181) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3181 (by decide) (by norm_num) (by norm_num)
lemma dvd_1061_aux (n : ℕ) (hn : n = 3181) : 1061 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3181 (by decide)
  rw [gcd_1061_aux 3181 rfl] at h
  have h_calc : 2 + 3181 / 1 = 3183 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1061 3183 (x_seq (3181 - 1)) (by decide)
lemma dvd_1061 : 1061 ∣ x_seq (1061^2 - 1) := by
  have h_dvd : x_seq 3181 ∣ x_seq (1061^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1061_aux 3181 rfl) h_dvd
lemma gcd_1063_aux (n : ℕ) (hn : n = 1061) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1061 (by decide) (by norm_num) (by norm_num)
lemma dvd_1063_aux (n : ℕ) (hn : n = 1061) : 1063 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1061 (by decide)
  rw [gcd_1063_aux 1061 rfl] at h
  have h_calc : 2 + 1061 / 1 = 1063 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1063 1063 (x_seq (1061 - 1)) (by decide)
lemma dvd_1063 : 1063 ∣ x_seq (1063^2 - 1) := by
  have h_dvd : x_seq 1061 ∣ x_seq (1063^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1063_aux 1061 rfl) h_dvd
lemma gcd_1069_aux (n : ℕ) (hn : n = 7481) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7481 (by decide) (by norm_num) (by norm_num)
lemma dvd_1069_aux (n : ℕ) (hn : n = 7481) : 1069 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7481 (by decide)
  rw [gcd_1069_aux 7481 rfl] at h
  have h_calc : 2 + 7481 / 1 = 7483 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1069 7483 (x_seq (7481 - 1)) (by decide)
lemma dvd_1069 : 1069 ∣ x_seq (1069^2 - 1) := by
  have h_dvd : x_seq 7481 ∣ x_seq (1069^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1069_aux 7481 rfl) h_dvd
lemma gcd_1087_aux (n : ℕ) (hn : n = 7607) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 7607 (by decide) (by norm_num) (by norm_num)
lemma dvd_1087_aux (n : ℕ) (hn : n = 7607) : 1087 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7607 (by decide)
  rw [gcd_1087_aux 7607 rfl] at h
  have h_calc : 2 + 7607 / 1 = 7609 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1087 7609 (x_seq (7607 - 1)) (by decide)
lemma dvd_1087 : 1087 ∣ x_seq (1087^2 - 1) := by
  have h_dvd : x_seq 7607 ∣ x_seq (1087^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1087_aux 7607 rfl) h_dvd
lemma gcd_1091_aux (n : ℕ) (hn : n = 3271) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3271 (by decide) (by norm_num) (by norm_num)
lemma dvd_1091_aux (n : ℕ) (hn : n = 3271) : 1091 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3271 (by decide)
  rw [gcd_1091_aux 3271 rfl] at h
  have h_calc : 2 + 3271 / 1 = 3273 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1091 3273 (x_seq (3271 - 1)) (by decide)
lemma dvd_1091 : 1091 ∣ x_seq (1091^2 - 1) := by
  have h_dvd : x_seq 3271 ∣ x_seq (1091^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1091_aux 3271 rfl) h_dvd
lemma gcd_1093_aux (n : ℕ) (hn : n = 1091) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 1091 (by decide) (by norm_num) (by norm_num)
lemma dvd_1093_aux (n : ℕ) (hn : n = 1091) : 1093 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 1091 (by decide)
  rw [gcd_1093_aux 1091 rfl] at h
  have h_calc : 2 + 1091 / 1 = 1093 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1093 1093 (x_seq (1091 - 1)) (by decide)
lemma dvd_1093 : 1093 ∣ x_seq (1093^2 - 1) := by
  have h_dvd : x_seq 1091 ∣ x_seq (1093^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1093_aux 1091 rfl) h_dvd
lemma gcd_1097_aux (n : ℕ) (hn : n = 5483) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 5483 (by decide) (by norm_num) (by norm_num)
lemma dvd_1097_aux (n : ℕ) (hn : n = 5483) : 1097 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 5483 (by decide)
  rw [gcd_1097_aux 5483 rfl] at h
  have h_calc : 2 + 5483 / 1 = 5485 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1097 5485 (x_seq (5483 - 1)) (by decide)
lemma dvd_1097 : 1097 ∣ x_seq (1097^2 - 1) := by
  have h_dvd : x_seq 5483 ∣ x_seq (1097^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1097_aux 5483 rfl) h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_1097 (r : ℕ) (hr_le : r ≤ 1097) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 509
  · exact prime_dvd_x_seq_sq_sub_one_bounded_509 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 510) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 511) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 512) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 513) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 514) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 515) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 516) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 517) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 518) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 519) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 520) hr |>.elim
    · exact dvd_521
    · exact (by decide : ¬ Nat.Prime 522) hr |>.elim
    · exact dvd_523
    · exact (by decide : ¬ Nat.Prime 524) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 525) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 526) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 527) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 528) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 529) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 530) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 531) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 532) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 533) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 534) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 535) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 536) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 537) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 538) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 539) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 540) hr |>.elim
    · exact dvd_541
    · exact (by decide : ¬ Nat.Prime 542) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 543) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 544) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 545) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 546) hr |>.elim
    · exact dvd_547
    · exact (by decide : ¬ Nat.Prime 548) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 549) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 550) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 551) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 552) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 553) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 554) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 555) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 556) hr |>.elim
    · exact dvd_557
    · exact (by decide : ¬ Nat.Prime 558) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 559) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 560) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 561) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 562) hr |>.elim
    · exact dvd_563
    · exact (by decide : ¬ Nat.Prime 564) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 565) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 566) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 567) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 568) hr |>.elim
    · exact dvd_569
    · exact (by decide : ¬ Nat.Prime 570) hr |>.elim
    · exact dvd_571
    · exact (by decide : ¬ Nat.Prime 572) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 573) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 574) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 575) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 576) hr |>.elim
    · exact dvd_577
    · exact (by decide : ¬ Nat.Prime 578) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 579) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 580) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 581) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 582) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 583) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 584) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 585) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 586) hr |>.elim
    · exact dvd_587
    · exact (by decide : ¬ Nat.Prime 588) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 589) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 590) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 591) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 592) hr |>.elim
    · exact dvd_593
    · exact (by decide : ¬ Nat.Prime 594) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 595) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 596) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 597) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 598) hr |>.elim
    · exact dvd_599
    · exact (by decide : ¬ Nat.Prime 600) hr |>.elim
    · exact dvd_601
    · exact (by decide : ¬ Nat.Prime 602) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 603) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 604) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 605) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 606) hr |>.elim
    · exact dvd_607
    · exact (by decide : ¬ Nat.Prime 608) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 609) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 610) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 611) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 612) hr |>.elim
    · exact dvd_613
    · exact (by decide : ¬ Nat.Prime 614) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 615) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 616) hr |>.elim
    · exact dvd_617
    · exact (by decide : ¬ Nat.Prime 618) hr |>.elim
    · exact dvd_619
    · exact (by decide : ¬ Nat.Prime 620) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 621) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 622) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 623) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 624) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 625) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 626) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 627) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 628) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 629) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 630) hr |>.elim
    · exact dvd_631
    · exact (by decide : ¬ Nat.Prime 632) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 633) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 634) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 635) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 636) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 637) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 638) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 639) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 640) hr |>.elim
    · exact dvd_641
    · exact (by decide : ¬ Nat.Prime 642) hr |>.elim
    · exact dvd_643
    · exact (by decide : ¬ Nat.Prime 644) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 645) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 646) hr |>.elim
    · exact dvd_647
    · exact (by decide : ¬ Nat.Prime 648) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 649) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 650) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 651) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 652) hr |>.elim
    · exact dvd_653
    · exact (by decide : ¬ Nat.Prime 654) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 655) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 656) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 657) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 658) hr |>.elim
    · exact dvd_659
    · exact (by decide : ¬ Nat.Prime 660) hr |>.elim
    · exact dvd_661
    · exact (by decide : ¬ Nat.Prime 662) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 663) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 664) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 665) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 666) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 667) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 668) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 669) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 670) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 671) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 672) hr |>.elim
    · exact dvd_673
    · exact (by decide : ¬ Nat.Prime 674) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 675) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 676) hr |>.elim
    · exact dvd_677
    · exact (by decide : ¬ Nat.Prime 678) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 679) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 680) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 681) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 682) hr |>.elim
    · exact dvd_683
    · exact (by decide : ¬ Nat.Prime 684) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 685) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 686) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 687) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 688) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 689) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 690) hr |>.elim
    · exact dvd_691
    · exact (by decide : ¬ Nat.Prime 692) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 693) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 694) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 695) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 696) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 697) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 698) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 699) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 700) hr |>.elim
    · exact dvd_701
    · exact (by decide : ¬ Nat.Prime 702) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 703) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 704) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 705) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 706) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 707) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 708) hr |>.elim
    · exact dvd_709
    · exact (by decide : ¬ Nat.Prime 710) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 711) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 712) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 713) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 714) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 715) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 716) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 717) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 718) hr |>.elim
    · exact dvd_719
    · exact (by decide : ¬ Nat.Prime 720) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 721) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 722) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 723) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 724) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 725) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 726) hr |>.elim
    · exact dvd_727
    · exact (by decide : ¬ Nat.Prime 728) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 729) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 730) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 731) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 732) hr |>.elim
    · exact dvd_733
    · exact (by decide : ¬ Nat.Prime 734) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 735) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 736) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 737) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 738) hr |>.elim
    · exact dvd_739
    · exact (by decide : ¬ Nat.Prime 740) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 741) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 742) hr |>.elim
    · exact dvd_743
    · exact (by decide : ¬ Nat.Prime 744) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 745) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 746) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 747) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 748) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 749) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 750) hr |>.elim
    · exact dvd_751
    · exact (by decide : ¬ Nat.Prime 752) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 753) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 754) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 755) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 756) hr |>.elim
    · exact dvd_757
    · exact (by decide : ¬ Nat.Prime 758) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 759) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 760) hr |>.elim
    · exact dvd_761
    · exact (by decide : ¬ Nat.Prime 762) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 763) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 764) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 765) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 766) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 767) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 768) hr |>.elim
    · exact dvd_769
    · exact (by decide : ¬ Nat.Prime 770) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 771) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 772) hr |>.elim
    · exact dvd_773
    · exact (by decide : ¬ Nat.Prime 774) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 775) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 776) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 777) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 778) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 779) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 780) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 781) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 782) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 783) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 784) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 785) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 786) hr |>.elim
    · exact dvd_787
    · exact (by decide : ¬ Nat.Prime 788) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 789) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 790) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 791) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 792) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 793) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 794) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 795) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 796) hr |>.elim
    · exact dvd_797
    · exact (by decide : ¬ Nat.Prime 798) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 799) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 800) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 801) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 802) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 803) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 804) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 805) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 806) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 807) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 808) hr |>.elim
    · exact dvd_809
    · exact (by decide : ¬ Nat.Prime 810) hr |>.elim
    · exact dvd_811
    · exact (by decide : ¬ Nat.Prime 812) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 813) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 814) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 815) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 816) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 817) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 818) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 819) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 820) hr |>.elim
    · exact dvd_821
    · exact (by decide : ¬ Nat.Prime 822) hr |>.elim
    · exact dvd_823
    · exact (by decide : ¬ Nat.Prime 824) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 825) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 826) hr |>.elim
    · exact dvd_827
    · exact (by decide : ¬ Nat.Prime 828) hr |>.elim
    · exact dvd_829
    · exact (by decide : ¬ Nat.Prime 830) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 831) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 832) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 833) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 834) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 835) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 836) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 837) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 838) hr |>.elim
    · exact dvd_839
    · exact (by decide : ¬ Nat.Prime 840) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 841) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 842) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 843) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 844) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 845) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 846) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 847) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 848) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 849) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 850) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 851) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 852) hr |>.elim
    · exact dvd_853
    · exact (by decide : ¬ Nat.Prime 854) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 855) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 856) hr |>.elim
    · exact dvd_857
    · exact (by decide : ¬ Nat.Prime 858) hr |>.elim
    · exact dvd_859
    · exact (by decide : ¬ Nat.Prime 860) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 861) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 862) hr |>.elim
    · exact dvd_863
    · exact (by decide : ¬ Nat.Prime 864) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 865) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 866) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 867) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 868) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 869) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 870) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 871) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 872) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 873) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 874) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 875) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 876) hr |>.elim
    · exact dvd_877
    · exact (by decide : ¬ Nat.Prime 878) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 879) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 880) hr |>.elim
    · exact dvd_881
    · exact (by decide : ¬ Nat.Prime 882) hr |>.elim
    · exact dvd_883
    · exact (by decide : ¬ Nat.Prime 884) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 885) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 886) hr |>.elim
    · exact dvd_887
    · exact (by decide : ¬ Nat.Prime 888) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 889) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 890) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 891) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 892) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 893) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 894) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 895) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 896) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 897) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 898) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 899) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 900) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 901) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 902) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 903) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 904) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 905) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 906) hr |>.elim
    · exact dvd_907
    · exact (by decide : ¬ Nat.Prime 908) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 909) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 910) hr |>.elim
    · exact dvd_911
    · exact (by decide : ¬ Nat.Prime 912) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 913) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 914) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 915) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 916) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 917) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 918) hr |>.elim
    · exact dvd_919
    · exact (by decide : ¬ Nat.Prime 920) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 921) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 922) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 923) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 924) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 925) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 926) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 927) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 928) hr |>.elim
    · exact dvd_929
    · exact (by decide : ¬ Nat.Prime 930) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 931) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 932) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 933) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 934) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 935) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 936) hr |>.elim
    · exact dvd_937
    · exact (by decide : ¬ Nat.Prime 938) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 939) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 940) hr |>.elim
    · exact dvd_941
    · exact (by decide : ¬ Nat.Prime 942) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 943) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 944) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 945) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 946) hr |>.elim
    · exact dvd_947
    · exact (by decide : ¬ Nat.Prime 948) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 949) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 950) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 951) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 952) hr |>.elim
    · exact dvd_953
    · exact (by decide : ¬ Nat.Prime 954) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 955) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 956) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 957) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 958) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 959) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 960) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 961) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 962) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 963) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 964) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 965) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 966) hr |>.elim
    · exact dvd_967
    · exact (by decide : ¬ Nat.Prime 968) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 969) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 970) hr |>.elim
    · exact dvd_971
    · exact (by decide : ¬ Nat.Prime 972) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 973) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 974) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 975) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 976) hr |>.elim
    · exact dvd_977
    · exact (by decide : ¬ Nat.Prime 978) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 979) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 980) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 981) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 982) hr |>.elim
    · exact dvd_983
    · exact (by decide : ¬ Nat.Prime 984) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 985) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 986) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 987) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 988) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 989) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 990) hr |>.elim
    · exact dvd_991
    · exact (by decide : ¬ Nat.Prime 992) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 993) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 994) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 995) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 996) hr |>.elim
    · exact dvd_997
    · exact (by decide : ¬ Nat.Prime 998) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 999) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1000) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1001) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1002) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1003) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1004) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1005) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1006) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1007) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1008) hr |>.elim
    · exact dvd_1009
    · exact (by decide : ¬ Nat.Prime 1010) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1011) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1012) hr |>.elim
    · exact dvd_1013
    · exact (by decide : ¬ Nat.Prime 1014) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1015) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1016) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1017) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1018) hr |>.elim
    · exact dvd_1019
    · exact (by decide : ¬ Nat.Prime 1020) hr |>.elim
    · exact dvd_1021
    · exact (by decide : ¬ Nat.Prime 1022) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1023) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1024) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1025) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1026) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1027) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1028) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1029) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1030) hr |>.elim
    · exact dvd_1031
    · exact (by decide : ¬ Nat.Prime 1032) hr |>.elim
    · exact dvd_1033
    · exact (by decide : ¬ Nat.Prime 1034) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1035) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1036) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1037) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1038) hr |>.elim
    · exact dvd_1039
    · exact (by decide : ¬ Nat.Prime 1040) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1041) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1042) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1043) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1044) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1045) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1046) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1047) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1048) hr |>.elim
    · exact dvd_1049
    · exact (by decide : ¬ Nat.Prime 1050) hr |>.elim
    · exact dvd_1051
    · exact (by decide : ¬ Nat.Prime 1052) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1053) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1054) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1055) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1056) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1057) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1058) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1059) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1060) hr |>.elim
    · exact dvd_1061
    · exact (by decide : ¬ Nat.Prime 1062) hr |>.elim
    · exact dvd_1063
    · exact (by decide : ¬ Nat.Prime 1064) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1065) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1066) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1067) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1068) hr |>.elim
    · exact dvd_1069
    · exact (by decide : ¬ Nat.Prime 1070) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1071) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1072) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1073) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1074) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1075) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1076) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1077) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1078) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1079) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1080) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1081) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1082) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1083) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1084) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1085) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1086) hr |>.elim
    · exact dvd_1087
    · exact (by decide : ¬ Nat.Prime 1088) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1089) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1090) hr |>.elim
    · exact dvd_1091
    · exact (by decide : ¬ Nat.Prime 1092) hr |>.elim
    · exact dvd_1093
    · exact (by decide : ¬ Nat.Prime 1094) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1095) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1096) hr |>.elim
    · exact dvd_1097


lemma gcd_1103_aux (n : ℕ) (hn : n = 3307) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3307 (by decide) (by norm_num) (by norm_num)

lemma dvd_1103_aux (n : ℕ) (hn : n = 3307) : 1103 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3307 (by decide)
  rw [gcd_1103_aux 3307 rfl] at h
  have h_calc : 2 + 3307 / 1 = 3309 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1103 3309 (x_seq (3307 - 1)) (by decide)

lemma dvd_1103 : 1103 ∣ x_seq (1103^2 - 1) := by
  have h_dvd : x_seq 3307 ∣ x_seq (1103^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1103_aux 3307 rfl) h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_1103 (r : ℕ) (hr_le : r ≤ 1103) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 1097
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1097 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 1098) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1099) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1100) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1101) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1102) hr |>.elim
    · exact dvd_1103


lemma gcd_1109_aux (n : ℕ) (hn : n = 12197) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 12197 (by decide) (by norm_num) (by norm_num)

lemma dvd_1109_aux (n : ℕ) (hn : n = 12197) : 1109 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 12197 (by decide)
  rw [gcd_1109_aux 12197 rfl] at h
  have h_calc : 2 + 12197 / 1 = 12199 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1109 12199 (x_seq (12197 - 1)) (by decide)

lemma dvd_1109 : 1109 ∣ x_seq (1109^2 - 1) := by
  have h_dvd : x_seq 12197 ∣ x_seq (1109^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1109_aux 12197 rfl) h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_1109 (r : ℕ) (hr_le : r ≤ 1109) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 1103
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1103 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 1104) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1105) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1106) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1107) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1108) hr |>.elim
    · exact dvd_1109



lemma r_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : r % 3 = 1 ∨ r % 3 = 2 := by
  have h_mod_lt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  have : r % 3 ≠ 0 := by
    intro h_mod_zero
    have h_dvd : 3 ∣ r := Nat.dvd_of_mod_eq_zero h_mod_zero
    have h_eq : r = 3 := by
      rcases hr.eq_one_or_self_of_dvd 3 h_dvd with h_one | h_self
      · contradiction
      · exact h_self.symm
    omega
  omega

lemma r_sq_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : r^2 % 3 = 1 := by
  have h_mod := r_mod_three r hr hr_ge
  have h_sq_mod : r^2 % 3 = (r % 3 * (r % 3)) % 3 := by
    rw [Nat.pow_two]
    exact Nat.mul_mod r r 3
  rcases h_mod with h1 | h2
  · rw [h_sq_mod, h1]
  · rw [h_sq_mod, h2]

lemma r_sq_plus_two_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : (r^2 + 2) % 3 = 0 := by
  have h_sq := r_sq_mod_three r hr hr_ge
  have h_add : (r^2 + 2) % 3 = (r^2 % 3 + 2) % 3 := Nat.add_mod (r^2) 2 3
  rw [h_add, h_sq]

lemma r_sq_plus_two_not_prime (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : ¬ Nat.Prime (r^2 + 2) := by
  intro h_prime
  have h_mod := r_sq_plus_two_mod_three r hr hr_ge
  have h_dvd : 3 ∣ r^2 + 2 := Nat.dvd_of_mod_eq_zero h_mod
  have h_eq : r^2 + 2 = 3 := by
    rcases h_prime.eq_one_or_self_of_dvd 3 h_dvd with h_one | h_self
    · contradiction
    · exact h_self.symm
  have h_r_sq_ge4 : r^2 ≥ 1216609 := by
    have h_mul : r * r ≥ 1103 * 1103 := Nat.mul_le_mul hr_ge hr_ge
    rw [← Nat.pow_two] at h_mul
    exact h_mul
  omega

lemma g_eq_one_for_p (p : ℕ) (hp : Nat.Prime p) (h_gt : p ≥ 4)
  (h1 : ¬ p ∣ x_seq (p - 3)) (h2 : p ∣ x_seq (p - 2)) :
  Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
  set g := Nat.gcd (x_seq (p - 3)) (p - 2)
  by_cases hg_eq1 : g = 1
  · exact hg_eq1
  · have hp_gt_2 : p ≥ 2 := Nat.Prime.two_le hp
    have h_p2 : p - 2 > 0 := by omega
    have hg_gt1 : g > 1 := by
      have : g > 0 := Nat.gcd_pos_of_pos_right _ h_p2
      omega
    have h_recurrence := x_seq_step_eq_gen (p - 2) (by omega)
    have h_eq_sub : p - 2 - 1 = p - 3 := by omega
    rw [h_eq_sub] at h_recurrence
    have h_dvd_sum : p ∣ 2 + (p - 2) / g := by
      have h_mul : p ∣ x_seq (p - 3) * (2 + (p - 2)/g) := by
        rw [← h_recurrence]
        exact h2
      exact (Nat.Prime.dvd_mul hp).mp h_mul |>.resolve_left h1
    set m := (p - 2) / g
    have h_dvd_sum_m : p ∣ 2 + m := h_dvd_sum
    have h_eq_g_m : g * m = p - 2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rcases h_dvd_sum_m with ⟨k, hk⟩
    have h_eq_mul : g * (2 + m) = g * (p * k) := by rw [hk]
    have h_distrib : g * (2 + m) = 2 * g + g * m := by ring
    rw [h_distrib, h_eq_g_m] at h_eq_mul
    have h_eq_sub_2 : 2 * g - 2 = p * (g * k - 1) := by
      have h_comm : g * (p * k) = p * (g * k) := by ring
      rw [h_comm] at h_eq_mul
      rw [Nat.mul_sub_left_distrib]
      rw [Nat.mul_one]
      omega
    have h_dvd_2_g_2 : p ∣ 2 * g - 2 := by
      rw [h_eq_sub_2]
      exact dvd_mul_right p (g * k - 1)
    have hr_dvd_g_1 : p ∣ g - 1 := by
      have h_ring : 2 * g - 2 = 2 * (g - 1) := by omega
      rw [h_ring] at h_dvd_2_g_2
      have h_not_dvd_2 : ¬ p ∣ 2 := by
        intro h_dvd_2
        have : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
        omega
      exact (Nat.Prime.dvd_mul hp).mp h_dvd_2_g_2 |>.resolve_left h_not_dvd_2
    have hg_ge_p : g ≥ p + 1 := by
      rcases hr_dvd_g_1 with ⟨k2, hk2⟩
      have hk2_pos : k2 > 0 := by
        by_contra h_zero
        have : k2 = 0 := by omega
        rw [this] at hk2
        omega
      have : g - 1 ≥ p := by
        calc g - 1 = p * k2 := hk2
        _ ≥ p * 1 := Nat.mul_le_mul_left p hk2_pos
        _ = p := by ring
      omega
    have hg_dvd : g ∣ p - 2 := Nat.gcd_dvd_right _ _
    have h_le_g : g ≤ p - 2 := Nat.le_of_dvd h_p2 hg_dvd
    omega


lemma prime_not_dvd_x_seq_bounded_1103 (p : ℕ) (hp_lt : p < 1229883) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
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
        have h_dvd1_orig := h_dvd1
        have h_step2 := x_seq_step_eq_gen (p - 2) (by omega)
        rw [h_step2] at h_dvd1
        rw [Nat.Prime.dvd_mul hp] at h_dvd1
        rcases h_dvd1 with h_dvd3 | h_dvd4
        · have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp h_dvd3
          omega
        · clear h_step1 h_step2
          have h_gcd_eq1 : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
            apply g_eq_one_for_p p hp (by omega)
            · intro hp_dvd
              have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp hp_dvd
              omega
            · exact h_dvd1_orig
          have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
          set r := Nat.minFac (p - 2)
          have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
          have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
          have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
          have hr_le : r ≤ 1103 := by
            by_contra h_gt
            have hr_ge : r ≥ 1104 := by omega
            have hr_lt_1109 : r < 1109 := by
              by_contra h_ge'
              have : r ≥ 1109 := by omega
              have : r^2 ≥ 1229881 := by nlinarith
              omega
            interval_cases r
            · exact (by decide : ¬ Nat.Prime 1104) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1105) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1106) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1107) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1108) hr_prime |>.elim
          have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_1103 r hr_le hr_prime
          have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
          have h_r2_sub_1_pos : r^2 - 1 > 0 := by
            have : r ≥ 2 := Nat.Prime.two_le hr_prime
            have : r^2 ≥ 4 := by nlinarith
            omega
          have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
          have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
          have h_r_dvd_gcd : r ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_r_dvd_x hr_dvd
          rw [h_gcd_eq1] at h_r_dvd_gcd
          have : r ∣ 1 := h_r_dvd_gcd
          have : r = 1 := Nat.eq_one_of_dvd_one this
          have : r ≥ 2 := Nat.Prime.two_le hr_prime
          omega
      · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
        have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
        contradiction


lemma prime_not_dvd_x_seq_bounded_1109 (p : ℕ) (hp_lt : p < 1247689) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
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
        have h_dvd1_orig := h_dvd1
        have h_step2 := x_seq_step_eq_gen (p - 2) (by omega)
        rw [h_step2] at h_dvd1
        rw [Nat.Prime.dvd_mul hp] at h_dvd1
        rcases h_dvd1 with h_dvd3 | h_dvd4
        · have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp h_dvd3
          omega
        · clear h_step1 h_step2
          have h_gcd_eq1 : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
            apply g_eq_one_for_p p hp (by omega)
            · intro hp_dvd
              have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp hp_dvd
              omega
            · exact h_dvd1_orig
          have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
          set r := Nat.minFac (p - 2)
          have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
          have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
          have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
          have hr_le : r ≤ 1109 := by
            by_contra h_gt
            have hr_ge : r ≥ 1110 := by omega
            have hr_lt_1117 : r < 1117 := by
              by_contra h_ge'
              have : r ≥ 1117 := by omega
              have : r^2 ≥ 1247689 := by nlinarith
              omega
            interval_cases r
            · exact (by decide : ¬ Nat.Prime 1110) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1111) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1112) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1113) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1114) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1115) hr_prime |>.elim
            · exact (by decide : ¬ Nat.Prime 1116) hr_prime |>.elim
          have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_1109 r hr_le hr_prime
          have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
          have h_r2_sub_1_pos : r^2 - 1 > 0 := by
            have : r ≥ 2 := Nat.Prime.two_le hr_prime
            have : r^2 ≥ 4 := by nlinarith
            omega
          have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
          have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
          have h_r_dvd_gcd : r ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_r_dvd_x hr_dvd
          rw [h_gcd_eq1] at h_r_dvd_gcd
          have : r ∣ 1 := h_r_dvd_gcd
          have : r = 1 := Nat.eq_one_of_dvd_one this
          have : r ≥ 2 := Nat.Prime.two_le hr_prime
          omega
      · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
        have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
        contradiction

lemma gcd_1117_aux (n : ℕ) (hn : n = 7817) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_bounded_1103 7817 (by decide) (by norm_num) (by norm_num)

lemma dvd_1117_aux (n : ℕ) (hn : n = 7817) : 1117 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 7817 (by decide)
  rw [gcd_1117_aux 7817 rfl] at h
  have h_calc : 2 + 7817 / 1 = 7819 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1117 7819 (x_seq (7817 - 1)) (by decide)

lemma dvd_1117 : 1117 ∣ x_seq (1117^2 - 1) := by
  have h_dvd : x_seq 7817 ∣ x_seq (1117^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1117_aux 7817 rfl) h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_1117 (r : ℕ) (hr_le : r ≤ 1117) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 1109
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1109 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 1110) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1111) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1112) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1113) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1114) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1115) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1116) hr |>.elim
    · exact dvd_1117


def joint_induction_pred (p : ℕ) : Prop :=
  (Nat.Prime p → ¬ Nat.Prime (p - 2) → Nat.gcd (x_seq (p - 1)) p = 1) ∧
  (∀ r, Nat.Prime r → r ≤ 1117 ∨ r^2 - 2 < p - 4 ∨ ((r^2 - 2 = p - 5 ∨ r^2 - 2 = p - 4 ∨ r^2 - 2 = p - 3 ∨ r^2 - 2 = p - 2) ∧ ¬ Nat.Prime p) → r ∣ x_seq (r^2 - 1))

lemma joint_induction (p : ℕ) : joint_induction_pred p := by
  induction' p using Nat.strong_induction_on with p ih
  by_cases hp_lt : p < 1229883
  · constructor
    · intro hp hp2
      exact prime_not_dvd_x_seq_bounded_1103 p hp_lt hp hp2
    · intro r hr h_lt
      rcases h_lt with h_lt | h_lt | h_lt
      · exact prime_dvd_x_seq_sq_sub_one_bounded_1117 r h_lt hr
      · by_cases hr_le1109 : r ≤ 1109
        · exact prime_dvd_x_seq_sq_sub_one_bounded_1109 r hr_le1109 hr
        · have hr_ge1117 : r ≥ 1117 := by
            by_contra h_lt'
            have : r < 1117 := by omega
            have : r ≥ 1110 := by omega
            interval_cases r
            · exact (by decide : ¬ Nat.Prime 1110) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1111) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1112) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1113) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1114) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1115) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1116) hr |>.elim
          have h_mul : r * r ≥ 1117 * 1117 := Nat.mul_le_mul hr_ge1117 hr_ge1117
          have h_r_sq : r^2 = r * r := by ring
          rw [h_r_sq] at h_lt
          omega
      · rcases h_lt with ⟨h_lt, _⟩
        by_cases hr_le1109 : r ≤ 1109
        · exact prime_dvd_x_seq_sq_sub_one_bounded_1109 r hr_le1109 hr
        · have hr_ge1117 : r ≥ 1117 := by
            by_contra h_lt'
            have : r < 1117 := by omega
            have : r ≥ 1110 := by omega
            interval_cases r
            · exact (by decide : ¬ Nat.Prime 1110) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1111) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1112) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1113) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1114) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1115) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1116) hr |>.elim
          have h_mul : r * r ≥ 1117 * 1117 := Nat.mul_le_mul hr_ge1117 hr_ge1117
          have h_r_sq : r^2 = r * r := by ring
          rw [h_r_sq] at h_lt
          omega
  · constructor
    · intro hp hp2
      have hp_ge : p ≥ 1229883 := by omega
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
          have h_dvd1_orig := h_dvd1
          have h_step2 := x_seq_step_eq_gen (p - 2) (by omega)
          rw [h_step2] at h_dvd1
          rw [Nat.Prime.dvd_mul hp] at h_dvd1
          rcases h_dvd1 with h_dvd3 | h_dvd4
          · have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp h_dvd3
            omega
          · clear h_step1 h_step2
            have h_gcd_eq1 : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
              apply g_eq_one_for_p p hp (by omega)
              · intro hp_dvd
                have h_le := max_prime_factor_x_seq (p - 3) (by omega) p hp hp_dvd
                omega
              · exact h_dvd1_orig
            have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
            set r := Nat.minFac (p - 2)
            have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
            have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
            have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
            by_cases hr_le1109 : r ≤ 1109
            · have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_1109 r hr_le1109 hr_prime
              have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
              have h_r2_sub_1_pos : r^2 - 1 > 0 := by
                have : r ≥ 2 := Nat.Prime.two_le hr_prime
                have : r^2 ≥ 4 := by nlinarith
                omega
              have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
              have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
              have h_r_dvd_gcd : r ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_r_dvd_x hr_dvd
              rw [h_gcd_eq1] at h_r_dvd_gcd
              have : r ∣ 1 := h_r_dvd_gcd
              have : r = 1 := Nat.eq_one_of_dvd_one this
              have : r ≥ 2 := Nat.Prime.two_le hr_prime
              omega
            · have hr_ge1117 : r ≥ 1117 := by
                by_contra h_lt
                have : r < 1117 := by omega
                have : r ≥ 1110 := by omega
                interval_cases r
                · exact (by decide : ¬ Nat.Prime 1110) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1111) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1112) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1113) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1114) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1115) hr_prime |>.elim
                · exact (by decide : ¬ Nat.Prime 1116) hr_prime |>.elim
              have h_ih := ih (p - 1) (by omega)
              have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := by
                by_cases hr_le1117 : r ≤ 1117
                · apply h_ih.2 r hr_prime
                  left
                  exact hr_le1117
                · apply h_ih.2 r hr_prime
                  right; left
                  by_contra h_contra
                  have h_eq_or : r^2 - 2 = p - 4 ∨ r^2 - 2 = p - 5 := by omega
                  rcases h_eq_or with hp_eq4 | hp_eq5
                  · have hp_eq : p = r^2 + 2 := by omega
                    have hr_ge1117 : r ≥ 1103 := by omega
                    have h_mod := r_sq_plus_two_mod_three r hr_prime hr_ge1117
                    have h_dvd : 3 ∣ p := by
                      rw [hp_eq]
                      exact Nat.dvd_of_mod_eq_zero h_mod
                    have hp_eq3 : p = 3 := by
                      rcases hp.eq_one_or_self_of_dvd 3 h_dvd with h1 | h2
                      · contradiction
                      · exact h2.symm
                    omega
                  · have hp_eq : p = r^2 + 3 := by omega
                    have hr_odd : ∃ k, r = 2 * k + 1 := by
                      use r / 2
                      have h_mod_or : r % 2 = 0 ∨ r % 2 = 1 := by omega
                      rcases h_mod_or with h_mod | h_mod
                      · have : 2 ∣ r := Nat.dvd_of_mod_eq_zero h_mod
                        rcases hr_prime.eq_one_or_self_of_dvd 2 this with h_one | h_self
                        · contradiction
                        · omega
                      · omega
                    rcases hr_odd with ⟨k, hk⟩
                    have hp_even : p = 2 * (2 * k^2 + 2 * k + 2) := by
                      rw [hk] at hp_eq
                      rw [hp_eq]
                      ring
                    have h_dvd : 2 ∣ p := by
                      rw [hp_even]
                      exact dvd_mul_right 2 _
                    have hp_eq2 : p = 2 := by
                      rcases hp.eq_one_or_self_of_dvd 2 h_dvd with h1 | h2
                      · contradiction
                      · exact h2.symm
                    omega
              have h_r2_sub_1_le_p3 : r^2 - 1 ≤ p - 3 := by omega
              have h_r2_sub_1_pos : r^2 - 1 > 0 := by
                have : r ≥ 2 := Nat.Prime.two_le hr_prime
                have : r^2 ≥ 4 := by nlinarith
                omega
              have h_x_dvd := x_seq_dvd_of_le (r^2 - 1) (p - 3) h_r2_sub_1_pos h_r2_sub_1_le_p3
              have h_r_dvd_x : r ∣ x_seq (p - 3) := dvd_trans h_r_dvd_sq h_x_dvd
              have h_r_dvd_gcd : r ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd h_r_dvd_x hr_dvd
              rw [h_gcd_eq1] at h_r_dvd_gcd
              have : r ∣ 1 := h_r_dvd_gcd
              have : r = 1 := Nat.eq_one_of_dvd_one this
              have : r ≥ 2 := Nat.Prime.two_le hr_prime
              omega
        · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
          have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
          contradiction
    · intro r hr h_lt
      rcases h_lt with hr_le1117 | h_lt | h_lt
      · exact prime_dvd_x_seq_sq_sub_one_bounded_1117 r hr_le1117 hr
      · by_cases hr_le1109 : r ≤ 1109
        · exact prime_dvd_x_seq_sq_sub_one_bounded_1109 r hr_le1109 hr
        · have hr_ge1117 : r ≥ 1117 := by
            by_contra h_lt'
            have : r < 1117 := by omega
            have : r ≥ 1110 := by omega
            interval_cases r
            · exact (by decide : ¬ Nat.Prime 1110) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1111) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1112) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1113) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1114) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1115) hr |>.elim
            · exact (by decide : ¬ Nat.Prime 1116) hr |>.elim
          by_cases hp_eq_1229883 : p = 1229883
          · subst hp_eq_1229883
            have h_mul : r * r ≥ 1117 * 1117 := Nat.mul_le_mul hr_ge1117 hr_ge1117
            have h_r_sq : r^2 = r * r := by ring
            rw [h_r_sq] at h_lt
            omega
          · have hp_gt_1229883 : p > 1229883 := by omega
            by_cases h_lt_p_sub_5 : r^2 - 2 < p - 5
            · have h_ih := ih (p - 1) (by omega)
              apply h_ih.2 r hr
              right; left; omega
            · have hp_sub_5_eq : p - 5 = r^2 - 2 := by omega
              have hr_ge1117 : r ≥ 1117 := by omega
              have hr_sq_ge : r^2 ≥ 1247689 := by
                have h_mul : r * r ≥ 1117 * 1117 := Nat.mul_le_mul hr_ge1117 hr_ge1117
                have h_r_sq : r^2 = r * r := by ring
                omega
              have h_ih := ih (p - 1) (by omega)
              apply h_ih.2 r hr
              right; right
              constructor
              · omega
              · have hp_eq : p - 1 = r^2 + 2 := by omega
                have hr_ge1103 : r ≥ 1103 := by omega
                have h_mod := r_sq_plus_two_mod_three r hr hr_ge1103
                have h_dvd : 3 ∣ p - 1 := by
                  rw [hp_eq]
                  exact Nat.dvd_of_mod_eq_zero h_mod
                intro hp_prime
                rcases hp_prime.eq_one_or_self_of_dvd 3 h_dvd with h1 | h2
                · contradiction
                · have : p - 1 = 3 := h2.symm
                  omega
      · rcases h_lt with ⟨h_le, hp_not_prime⟩
        by_cases hr_le1117 : r ≤ 1117
        · exact prime_dvd_x_seq_sq_sub_one_bounded_1117 r hr_le1117 hr
        · have hr_ge1117 : r ≥ 1117 := by omega
          have hr_sq_ge : r^2 ≥ 1247689 := by
            have h_mul : r * r ≥ 1117 * 1117 := Nat.mul_le_mul hr_ge1117 hr_ge1117
            have h_r_sq : r^2 = r * r := by ring
            omega
          have h_ih := ih (p - 1) (by omega)
          apply h_ih.2 r hr
          by_cases h_lt_p_sub_5 : r^2 - 2 < p - 5
          · right; left; omega
          · right; right
            by_cases hp2_eq : r^2 - 2 = p - 2
            · have hp_eq : p - 1 = r^2 - 1 := by omega
              have h_dvd : r - 1 ∣ p - 1 := by
                rw [hp_eq]
                have : r^2 - 1 = (r - 1) * (r + 1) := by
                  have h_sq : r^2 = r * r := by ring
                  rw [h_sq]
                  have : r ≥ 2 := Nat.Prime.two_le hr
                  have : r * r ≥ 1 := by nlinarith
                  zify
                  ring
                rw [this]
                exact dvd_mul_right (r - 1) (r + 1)
              have h_contra : ¬ Nat.Prime (p - 1) := by
                intro hp_prime
                rcases hp_prime.eq_one_or_self_of_dvd (r - 1) h_dvd with h1 | h2
                · omega
                · rw [hp_eq] at h2
                  have : r - 1 < r^2 - 1 := by
                    have h_sq : r^2 = r * r := by ring
                    rw [h_sq] at h2
                    rw [h_sq]
                    have : r ≥ 2 := Nat.Prime.two_le hr
                    have : r * r ≥ 1 := by nlinarith
                    zify
                    nlinarith
                  omega
              contradiction
            · constructor
              · omega
            · have h_cases : r^2 - 2 = p - 5 ∨ r^2 - 2 = p - 4 ∨ r^2 - 2 = p - 3 ∨ r^2 - 2 = p - 2 := by omega
              intro hp_prime
              rcases h_cases with hp5 | hp4 | hp3 | hp2
              · have hp_eq : p - 1 = r^2 + 2 := by omega
                have hr_ge1103 : r ≥ 1103 := by omega
                have h_mod := r_sq_plus_two_mod_three r hr hr_ge1103
                have h_dvd : 3 ∣ p - 1 := by
                  rw [hp_eq]
                  exact Nat.dvd_of_mod_eq_zero h_mod
                rcases hp_prime.eq_one_or_self_of_dvd 3 h_dvd with h1 | h2
                · contradiction
                · have : p - 1 = 3 := h2.symm
                  omega
              · have hp_eq : p - 1 = r^2 + 1 := by omega
                have hr_odd : ∃ k, r = 2 * k + 1 := by
                  use r / 2
                  have h_mod_or : r % 2 = 0 ∨ r % 2 = 1 := by omega
                  rcases h_mod_or with h_mod | h_mod
                  · have : 2 ∣ r := Nat.dvd_of_mod_eq_zero h_mod
                    rcases hr.eq_one_or_self_of_dvd 2 this with h_one | h_self
                    · contradiction
                    · omega
                  · omega
                rcases hr_odd with ⟨k, hk⟩
                have hp_even : p - 1 = 2 * (2 * k^2 + 2 * k + 1) := by
                  rw [hk] at hp_eq
                  rw [hp_eq]
                  ring
                have hdvd : 2 ∣ p - 1 := by
                  rw [hp_even]
                  exact dvd_mul_right 2 _
                rcases hp_prime.eq_one_or_self_of_dvd 2 hdvd with h1 | h2
                · contradiction
                · have : p - 1 = 2 := h2.symm
                  omega
              · have hp_eq : p - 1 = r^2 := by omega
                have h_dvd : r ∣ p - 1 := by
                  rw [hp_eq]
                  have : r^2 = r * r := by ring
                  rw [this]
                  exact dvd_mul_left r r
                rcases hp_prime.eq_one_or_self_of_dvd r h_dvd with h1 | h2
                · have : r = 1 := h1
                  omega
                · have : r = r^2 := h2.trans hp_eq
                  have : r ≥ 2 := Nat.Prime.two_le hr
                  nlinarith
              · have hp_eq : p - 1 = r^2 - 1 := by omega
                have h_dvd : r - 1 ∣ p - 1 := by
                  rw [hp_eq]
                  have : r^2 - 1 = (r - 1) * (r + 1) := by
                    have h_sq : r^2 = r * r := by ring
                    rw [h_sq]
                    have : r ≥ 2 := Nat.Prime.two_le hr
                    have : r * r ≥ 1 := by nlinarith
                    zify
                    ring
                  rw [this]
                  exact dvd_mul_right (r - 1) (r + 1)
                rcases hp_prime.eq_one_or_self_of_dvd (r - 1) h_dvd with h1 | h2
                · omega
                · rw [hp_eq] at h2
                  have : r - 1 < r^2 - 1 := by
                    have h_sq : r^2 = r * r := by ring
                    rw [h_sq] at h2
                    rw [h_sq]
                    have : r ≥ 2 := Nat.Prime.two_le hr
                    have : r * r ≥ 1 := by nlinarith
                    zify
                    nlinarith
                  omega

lemma prime_not_dvd_x_seq (p : ℕ) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  by_cases hp_lt2 : p < 1229883
  · exact prime_not_dvd_x_seq_bounded_1103 p hp_lt2 hp hp2
  · have h := joint_induction p
    exact h.1 hp hp2

theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hp2
  rw [A135508_p_eq p hp]
  rw [prime_not_dvd_x_seq p hp hp2]
  exact Nat.div_one p
