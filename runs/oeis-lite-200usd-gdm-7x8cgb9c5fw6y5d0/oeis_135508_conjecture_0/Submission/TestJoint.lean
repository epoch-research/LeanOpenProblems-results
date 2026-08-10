import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
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
  · cases' n with n\x27
    · simp [x_seq]
    · rw [x_seq]
      · have h1 : n\x27 + 1 > 0 := by omega
        have h2 : x_seq (n\x27 + 1) > 0 := ih h1
        omega
      · omega

lemma x_seq_dvd (n : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n
  · contradiction
  · rename_i n_1
    nth_rw 2 [x_seq]
    · have h1 : x_seq (n_1 + 1) ∣ 2 * x_seq (n_1 + 1) := dvd_mul_left _ _
      have h2 : x_seq (n_1 + 1) ∣ Nat.lcm (x_seq (n_1 + 1)) (n_1 + 1 + 1) := Nat.dvd_lcm_left _ _
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

lemma prime_dvd_x_seq_sq_sub_one (r : ℕ) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  induction' r using Nat.strong_induction_on with r ih
  sorry
