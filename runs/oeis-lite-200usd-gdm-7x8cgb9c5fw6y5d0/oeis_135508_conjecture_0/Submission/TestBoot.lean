import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

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

lemma A135508_eq (p : ℕ) (hp : Nat.Prime p) : A135508 (p - 1) = (x_seq p / x_seq (p - 1)) - 2 := by sorry
def A135508 (n : ℕ) : ℕ := sorry
lemma div_add_rule (a b c : ℕ) (ha : a > 0) : (a * b + c) / a = b + c / a := sorry
lemma lcm_def_eq (m n : ℕ) : Nat.lcm m n = m * n / Nat.gcd m n := rfl
lemma lcm_div_rule (a b : ℕ) (ha : a > 0) : Nat.lcm a b / a = b / Nat.gcd a b := sorry
lemma x_seq_div_eq (p : ℕ) (hp : Nat.Prime p) : x_seq p / x_seq (p - 1) = 2 + p / Nat.gcd (x_seq (p - 1)) p := sorry
lemma A135508_p_eq (p : ℕ) (hp : Nat.Prime p) : A135508 (p - 1) = p / Nat.gcd (x_seq (p - 1)) p := sorry
lemma x_seq_dvd (n : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + 1) := sorry
lemma x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (hab : a ≤ b) : x_seq a ∣ x_seq b := sorry
lemma gcd_prime_eq (a p : ℕ) (hp : Nat.Prime p) : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := sorry
lemma x_seq_div_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n / x_seq (n - 1) = 2 + n / Nat.gcd (x_seq (n - 1)) n := sorry
lemma x_seq_step_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n = x_seq (n - 1) * (2 + n / Nat.gcd (x_seq (n - 1)) n) := sorry
lemma max_prime_factor_x_seq (n : ℕ) (hn : n > 0) (r : ℕ) (hr : Nat.Prime r) (hd : r ∣ x_seq n) : r ≤ n + 2 := sorry
lemma prime_not_dvd_add (p h : ℕ) (hp : Nat.Prime p) (hp3 : p > 3) (hh : h ∣ p - 1) : ¬ p ∣ 2 + h := sorry

def x_seq_loop : ℕ → ℕ → ℕ → ℕ | 0, _, acc => acc | i + 1, idx, acc => x_seq_loop i (idx + 1) (2 * acc + Nat.lcm acc idx)
def x_seq_tail (n : ℕ) : ℕ := if n = 0 then 0 else x_seq_loop (n - 1) 2 1
lemma x_seq_eq_x_seq_tail (n : ℕ) : x_seq n = x_seq_tail n := sorry
lemma prime_not_dvd_x_seq_small (p : ℕ) (hp_lt : p < 600) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by sorry
lemma prime_dvd_x_seq_sq_sub_one_bounded (r : ℕ) (hr_lt : r < 15) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := sorry
lemma test_prime : Nat.Prime 2459 := by norm_num

lemma prime_not_dvd_x_seq_103 (p : ℕ) (hp_lt : p < 11451) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  by_cases hp_lt_600 : p < 600
  · exact prime_not_dvd_x_seq_small p hp_lt_600 hp hp2
  · sorry

lemma dvd_107_aux : 107 ∣ x_seq 2459 := by
  have h_step : x_seq 2459 = x_seq 2458 * (2 + 2459 / Nat.gcd (x_seq 2458) 2459) := by
    apply x_seq_step_eq_gen 2459 (by omega)
  have h_gcd : Nat.gcd (x_seq 2458) 2459 = 1 := prime_not_dvd_x_seq_103 2459 (by omega) (by norm_num) (by norm_num)
  rw [h_gcd] at h_step
  have h_div : 2459 / 1 = 2459 := Nat.div_one 2459
  rw [h_div] at h_step
  have h_add : 2 + 2459 = 2461 := by rfl
  rw [h_add] at h_step
  rw [h_step]
  have h_dvd_2461 : 107 ∣ 2461 := by
    use 23
    rfl
  exact dvd_mul_of_dvd_right h_dvd_2461 _
