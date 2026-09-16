import Mathlib

lemma n_le_choose_two (n : ℕ) (hn : 3 ≤ n) : n ≤ n * (n - 1) / 2 := by
  have H : n * 2 ≤ n * (n - 1) := by
    have : 2 ≤ n - 1 := by omega
    nlinarith
  have H2 : (n * 2) / 2 ≤ (n * (n - 1)) / 2 := Nat.div_le_div_right H
  have H3 : (n * 2) / 2 = n := Nat.mul_div_cancel n (by decide)
  rw [H3] at H2
  exact H2
