import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def x_seq_let : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 =>
  let prev := x_seq_let n
  2 * prev + Nat.lcm prev (n + 1)

lemma x_seq_let_eq_x_seq (n : ℕ) : x_seq_let n = x_seq n := by
  induction' n with n ih
  · rfl
  · cases' n with n'
    · rfl
    · change (let prev := x_seq_let (n' + 1); 2 * prev + Nat.lcm prev (n' + 2)) = 2 * (x_seq (n' + 1)) + Nat.lcm (x_seq (n' + 1)) (n' + 2)
      rw [ih]


lemma dvd_31 : 31 ∣ x_seq (31^2 - 1) := by decide

lemma dvd_37 : 37 ∣ x_seq (37^2 - 1) := by decide
lemma dvd_41 : 41 ∣ x_seq (41^2 - 1) := by decide
lemma dvd_43 : 43 ∣ x_seq (43^2 - 1) := by decide
lemma dvd_47 : 47 ∣ x_seq (47^2 - 1) := by decide

lemma dvd_53 : 53 ∣ x_seq (53^2 - 1) := by decide
lemma dvd_59 : 59 ∣ x_seq (59^2 - 1) := by decide
lemma dvd_61 : 61 ∣ x_seq (61^2 - 1) := by decide










