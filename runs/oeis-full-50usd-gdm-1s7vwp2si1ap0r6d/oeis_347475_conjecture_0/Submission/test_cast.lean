import Mathlib

theorem my_mock (x : ℕ) (h_cond : x * (x + 1) / 2 < 10^250) (hx : x ≥ 10^250) : False := by
  have h_bound : x * (x + 1) / 2 ≥ 10^250 := by
    have h1 : 2 > 0 := by decide
    change 10^250 ≤ x * (x + 1) / 2
    rw [Nat.le_div_iff_mul_le h1]
    have h2 : 10^250 * 2 ≤ x * 2 := by omega
    have h3 : x * 2 ≤ x * (x + 1) := Nat.mul_le_mul_left x (by omega)
    exact h2.trans h3
  omega
