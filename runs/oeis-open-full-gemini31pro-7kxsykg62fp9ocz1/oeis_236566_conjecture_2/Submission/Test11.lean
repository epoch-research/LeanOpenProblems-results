import Mathlib

lemma test (q p : ℕ) (hq : Nat.Prime q) (h_q_div : 2 * p - 1 ∣ q) : 2 * p - 1 = 1 ∨ 2 * p - 1 = q := by
  exact hq.eq_one_or_self_of_dvd _ h_q_div
