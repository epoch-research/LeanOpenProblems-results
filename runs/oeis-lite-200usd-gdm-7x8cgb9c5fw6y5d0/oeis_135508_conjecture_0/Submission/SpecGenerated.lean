import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
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

lemma dvd_149_aux : 149 ∣ x_seq 743 := by
      rw [x_seq_eq_x_seq_tail 743]
      decide
lemma dvd_149 : 149 ∣ x_seq (149^2 - 1) := by
  have h_dvd : x_seq 743 ∣ x_seq (149^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_149_aux h_dvd

lemma dvd_151_aux : 151 ∣ x_seq 149 := by
      rw [x_seq_eq_x_seq_tail 149]
      decide
lemma dvd_151 : 151 ∣ x_seq (151^2 - 1) := by
  have h_dvd : x_seq 149 ∣ x_seq (151^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_151_aux h_dvd

lemma dvd_157_aux : 157 ∣ x_seq 1097 := by
      rw [x_seq_eq_x_seq_tail 1097]
      decide
lemma dvd_157 : 157 ∣ x_seq (157^2 - 1) := by
  have h_dvd : x_seq 1097 ∣ x_seq (157^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_157_aux h_dvd

lemma dvd_163_aux : 163 ∣ x_seq 487 := by
      rw [x_seq_eq_x_seq_tail 487]
      decide
lemma dvd_163 : 163 ∣ x_seq (163^2 - 1) := by
  have h_dvd : x_seq 487 ∣ x_seq (163^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_163_aux h_dvd

lemma dvd_167_aux : 167 ∣ x_seq 499 := by
      rw [x_seq_eq_x_seq_tail 499]
      decide
lemma dvd_167 : 167 ∣ x_seq (167^2 - 1) := by
  have h_dvd : x_seq 499 ∣ x_seq (167^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_167_aux h_dvd

lemma dvd_173_aux : 173 ∣ x_seq 863 := by
      rw [x_seq_eq_x_seq_tail 863]
      decide
lemma dvd_173 : 173 ∣ x_seq (173^2 - 1) := by
  have h_dvd : x_seq 863 ∣ x_seq (173^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_173_aux h_dvd

lemma dvd_179_aux : 179 ∣ x_seq 2683 := by
      rw [x_seq_eq_x_seq_tail 2683]
      decide
lemma dvd_179 : 179 ∣ x_seq (179^2 - 1) := by
  have h_dvd : x_seq 2683 ∣ x_seq (179^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_179_aux h_dvd

lemma dvd_181_aux : 181 ∣ x_seq 179 := by
      rw [x_seq_eq_x_seq_tail 179]
      decide
lemma dvd_181 : 181 ∣ x_seq (181^2 - 1) := by
  have h_dvd : x_seq 179 ∣ x_seq (181^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_181_aux h_dvd

lemma dvd_191_aux : 191 ∣ x_seq 953 := by
      rw [x_seq_eq_x_seq_tail 953]
      decide
lemma dvd_191 : 191 ∣ x_seq (191^2 - 1) := by
  have h_dvd : x_seq 953 ∣ x_seq (191^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_191_aux h_dvd

lemma dvd_193_aux : 193 ∣ x_seq 191 := by
      rw [x_seq_eq_x_seq_tail 191]
      decide
lemma dvd_193 : 193 ∣ x_seq (193^2 - 1) := by
  have h_dvd : x_seq 191 ∣ x_seq (193^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_193_aux h_dvd

lemma dvd_197_aux : 197 ∣ x_seq 983 := by
      rw [x_seq_eq_x_seq_tail 983]
      decide
lemma dvd_197 : 197 ∣ x_seq (197^2 - 1) := by
  have h_dvd : x_seq 983 ∣ x_seq (197^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_197_aux h_dvd

lemma dvd_199_aux : 199 ∣ x_seq 197 := by
      rw [x_seq_eq_x_seq_tail 197]
      decide
lemma dvd_199 : 199 ∣ x_seq (199^2 - 1) := by
  have h_dvd : x_seq 197 ∣ x_seq (199^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_199_aux h_dvd

lemma dvd_211_aux : 211 ∣ x_seq 631 := by
      rw [x_seq_eq_x_seq_tail 631]
      decide
lemma dvd_211 : 211 ∣ x_seq (211^2 - 1) := by
  have h_dvd : x_seq 631 ∣ x_seq (211^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_211_aux h_dvd

lemma dvd_223_aux : 223 ∣ x_seq 1559 := by
      rw [x_seq_eq_x_seq_tail 1559]
      decide
lemma dvd_223 : 223 ∣ x_seq (223^2 - 1) := by
  have h_dvd : x_seq 1559 ∣ x_seq (223^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_223_aux h_dvd

lemma dvd_227_aux : 227 ∣ x_seq 6581 := by
      rw [x_seq_eq_x_seq_tail 6581]
      decide
lemma dvd_227 : 227 ∣ x_seq (227^2 - 1) := by
  have h_dvd : x_seq 6581 ∣ x_seq (227^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_227_aux h_dvd

lemma dvd_229_aux : 229 ∣ x_seq 227 := by
      rw [x_seq_eq_x_seq_tail 227]
      decide
lemma dvd_229 : 229 ∣ x_seq (229^2 - 1) := by
  have h_dvd : x_seq 227 ∣ x_seq (229^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_229_aux h_dvd

lemma dvd_233_aux : 233 ∣ x_seq 1163 := by
      rw [x_seq_eq_x_seq_tail 1163]
      decide
lemma dvd_233 : 233 ∣ x_seq (233^2 - 1) := by
  have h_dvd : x_seq 1163 ∣ x_seq (233^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_233_aux h_dvd

lemma dvd_239_aux : 239 ∣ x_seq 1193 := by
      rw [x_seq_eq_x_seq_tail 1193]
      decide
lemma dvd_239 : 239 ∣ x_seq (239^2 - 1) := by
  have h_dvd : x_seq 1193 ∣ x_seq (239^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_239_aux h_dvd

lemma dvd_241_aux : 241 ∣ x_seq 239 := by
      rw [x_seq_eq_x_seq_tail 239]
      decide
lemma dvd_241 : 241 ∣ x_seq (241^2 - 1) := by
  have h_dvd : x_seq 239 ∣ x_seq (241^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_241_aux h_dvd

lemma dvd_251_aux : 251 ∣ x_seq 751 := by
      rw [x_seq_eq_x_seq_tail 751]
      decide
lemma dvd_251 : 251 ∣ x_seq (251^2 - 1) := by
  have h_dvd : x_seq 751 ∣ x_seq (251^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_251_aux h_dvd

lemma dvd_257_aux : 257 ∣ x_seq 769 := by
      rw [x_seq_eq_x_seq_tail 769]
      decide
lemma dvd_257 : 257 ∣ x_seq (257^2 - 1) := by
  have h_dvd : x_seq 769 ∣ x_seq (257^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_257_aux h_dvd

lemma dvd_263_aux : 263 ∣ x_seq 787 := by
      rw [x_seq_eq_x_seq_tail 787]
      decide
lemma dvd_263 : 263 ∣ x_seq (263^2 - 1) := by
  have h_dvd : x_seq 787 ∣ x_seq (263^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_263_aux h_dvd

lemma dvd_269_aux : 269 ∣ x_seq 2957 := by
      rw [x_seq_eq_x_seq_tail 2957]
      decide
lemma dvd_269 : 269 ∣ x_seq (269^2 - 1) := by
  have h_dvd : x_seq 2957 ∣ x_seq (269^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_269_aux h_dvd

lemma dvd_271_aux : 271 ∣ x_seq 269 := by
      rw [x_seq_eq_x_seq_tail 269]
      decide
lemma dvd_271 : 271 ∣ x_seq (271^2 - 1) := by
  have h_dvd : x_seq 269 ∣ x_seq (271^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_271_aux h_dvd

lemma dvd_277_aux : 277 ∣ x_seq 4153 := by
      rw [x_seq_eq_x_seq_tail 4153]
      decide
lemma dvd_277 : 277 ∣ x_seq (277^2 - 1) := by
  have h_dvd : x_seq 4153 ∣ x_seq (277^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_277_aux h_dvd

lemma dvd_281_aux : 281 ∣ x_seq 3089 := by
      rw [x_seq_eq_x_seq_tail 3089]
      decide
lemma dvd_281 : 281 ∣ x_seq (281^2 - 1) := by
  have h_dvd : x_seq 3089 ∣ x_seq (281^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_281_aux h_dvd

lemma dvd_283_aux : 283 ∣ x_seq 281 := by
      rw [x_seq_eq_x_seq_tail 281]
      decide
lemma dvd_283 : 283 ∣ x_seq (283^2 - 1) := by
  have h_dvd : x_seq 281 ∣ x_seq (283^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_283_aux h_dvd

lemma dvd_293_aux : 293 ∣ x_seq 877 := by
      rw [x_seq_eq_x_seq_tail 877]
      decide
lemma dvd_293 : 293 ∣ x_seq (293^2 - 1) := by
  have h_dvd : x_seq 877 ∣ x_seq (293^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans dvd_293_aux h_dvd

lemma prime_dvd_x_seq_sq_sub_one_chunk_0 (r : ℕ) (hr_ge : r ≥ 15) (hr_le : r < 100) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  interval_cases r
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

lemma prime_dvd_x_seq_sq_sub_one_chunk_1 (r : ℕ) (hr_ge : r ≥ 100) (hr_le : r < 200) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  interval_cases r
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

lemma prime_dvd_x_seq_sq_sub_one_chunk_2 (r : ℕ) (hr_ge : r ≥ 200) (hr_le : r < 300) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  interval_cases r
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

lemma prime_dvd_x_seq_sq_sub_one_bounded_293 (r : ℕ) (hr_le : r ≤ 293) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r < 15
  · exact prime_dvd_x_seq_sq_sub_one_bounded r h_0 hr
  · by_cases h_chunk_0 : r < 100
    · exact prime_dvd_x_seq_sq_sub_one_chunk_0 r (by omega) h_chunk_0 hr
    · by_cases h_chunk_1 : r < 200
      · exact prime_dvd_x_seq_sq_sub_one_chunk_1 r (by omega) h_chunk_1 hr
      · exact prime_dvd_x_seq_sq_sub_one_chunk_2 r (by omega) (by omega) hr
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
          have hg_pos : g > 0 := Nat.gcd_pos_of_pos_right _ hq_pos
          have hg_cases : g = 1 ∨ g > 1 := by omega
          rcases hg_cases with hg_eq1 | hg_gt1
          · clear h_dvd4
            have h_minFac_sq := Nat.minFac_sq_le_self hq_pos hp2
            set r := Nat.minFac (p - 2)
            have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
            have hr_dvd : r ∣ p - 2 := Nat.minFac_dvd (p - 2)
            have hr_sq_le : r^2 ≤ p - 2 := h_minFac_sq
            have hr_le : r ≤ 293 := by
              by_cases hp_lt2 : p < 86438
              · have h_p2 : p - 2 < 86436 := by omega
                have : r^2 < 86436 := by nlinarith
                have : r < 294 := by nlinarith
                omega
              · sorry
            have h_r_dvd_sq : r ∣ x_seq (r^2 - 1) := prime_dvd_x_seq_sq_sub_one_bounded_293 r hr_le hr_prime
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
              have h_div_lt' : (p - 2) / g < p - 2 := by
                apply Nat.div_lt_self
                · omega
                · omega
              omega
            have h_sum_pos : 2 + (p - 2) / g > 0 := by
              have : (p - 2) / g ≥ 0 := Nat.zero_le _
              omega
            have : p ≤ 2 + (p - 2) / g := Nat.le_of_dvd h_sum_pos h_dvd4
            omega
      · have h_gcd_val := Nat.gcd_dvd_right (x_seq (p - 2)) (p - 1)
        have h_no_dvd := prime_not_dvd_add p ((p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) hp (by omega) (Nat.div_dvd_of_dvd h_gcd_val)
        contradiction

theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hp2
  rw [A135508_p_eq p hp]
  rw [prime_not_dvd_x_seq p hp hp2]
  exact Nat.div_one p
