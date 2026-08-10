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
  · cases' n with n_1
    · simp [x_seq]
    · rw [x_seq]
      · have h1 : n_1 + 1 > 0 := by omega
        have h2 : x_seq (n_1 + 1) > 0 := ih h1
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

-- we import the already checked prime_not_dvd_x_seq from Spec.lean by copying its statement or using it
-- wait, we can just assume it as a hypothesis or copy the small parts we need
-- Actually, we can define prime_not_dvd_x_seq_small which is in Spec.lean and decided for p < 600.
-- Wait, p = 2459 in TestBoot.lean is 2459, which is < 11451.
-- Since 5153 is prime, and 5153 - 2 = 5151 = 3 * 1717 (composite).
-- Is 5153 < 1042443? Yes!
-- So we can use prime_not_dvd_x_seq 5153 (which is proved in Spec.lean!)
-- But to compile this file on its own, we can just mock or define prime_not_dvd_x_seq_1031
