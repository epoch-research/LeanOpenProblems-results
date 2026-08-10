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

lemma prime_not_dvd_x_seq_small (p : ℕ) (hp_lt : p < 631) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := by
  revert hp hp2 hp_lt p
  decide

lemma prime_dvd_x_seq_sq_sub_one_bounded (r : ℕ) (hr_lt : r < 15) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  revert hr hr_lt r
  decide

lemma dvd_17 : 17 ∣ x_seq (17^2 - 1) := by decide
lemma dvd_19 : 19 ∣ x_seq (19^2 - 1) := by decide
lemma dvd_23 : 23 ∣ x_seq (23^2 - 1) := by decide

lemma prime_dvd_x_seq_sq_sub_one_bounded_23 (r : ℕ) (hr_le : r ≤ 23) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h : r < 15
  · exact prime_dvd_x_seq_sq_sub_one_bounded r h hr
  · have hr_cases : r = 17 ∨ r = 19 ∨ r = 23 := by
      have : r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (by decide : ¬ Nat.Prime 15) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 16) hr |>.elim
      · left; rfl
      · exact (by decide : ¬ Nat.Prime 18) hr |>.elim
      · right; left; rfl
      · exact (by decide : ¬ Nat.Prime 20) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 21) hr |>.elim
      · exact (by decide : ¬ Nat.Prime 22) hr |>.elim
      · right; right; rfl
    rcases hr_cases with rfl | rfl | rfl
    · exact dvd_17
    · exact dvd_19
    · exact dvd_23

