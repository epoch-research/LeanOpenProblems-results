import FormalConjectures.Util.ProblemImports

open Nat

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

def T (z : ℕ) : ℕ := z * (z + 1) / 2

lemma two_dvd_succ_mul (z : ℕ) : 2 ∣ z * (z + 1) := by
  cases Nat.even_or_odd z with
  | inl h => exact h.two_dvd.mul_right _
  | inr h =>
    have : Even (z + 1) := h.add_odd odd_one
    exact this.two_dvd.mul_left _

lemma T_mul_two (z : ℕ) : 2 * T z = z * (z + 1) := by
  rw [T, Nat.mul_div_cancel' (two_dvd_succ_mul z)]

/-- 8 T z + 1 = (2z+1)² -/
lemma eight_T_add_one (z : ℕ) : 8 * T z + 1 = (2 * z + 1) ^ 2 := by
  have h := T_mul_two z
  have : 8 * T z = 4 * (z * (z + 1)) := by
    calc 8 * T z = 4 * (2 * T z) := by ring
      _ = 4 * (z * (z + 1)) := by rw [h]
  rw [this]
  ring

/-- 8 y(y+1) + 2 = 2(2y+1)² -/
lemma eight_yy_add_two (y : ℕ) : 8 * (y * (y + 1)) + 2 = 2 * (2 * y + 1) ^ 2 := by
  ring

/--
Key identity:
`8 * (x² + y(y+1) + T z) + 3 = (2z+1)² + 2(2y+1)² + 8 x²`.
-/
lemma form_identity (x y z : ℕ) :
    8 * (x * x + y * (y + 1) + T z) + 3 =
      (2 * z + 1) ^ 2 + 2 * (2 * y + 1) ^ 2 + 8 * (x * x) := by
  nlinarith [eight_T_add_one z, eight_yy_add_two y]

lemma eq_iff_form (n x y z : ℕ) :
    x * x + y * (y + 1) + T z = n ↔
      (2 * z + 1) ^ 2 + 2 * (2 * y + 1) ^ 2 + 8 * (x * x) = 8 * n + 3 := by
  constructor
  · intro h; rw [← h, form_identity]
  · intro h
    have hid := form_identity x y z
    have : 8 * (x * x + y * (y + 1) + T z) = 8 * n := by
      omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) this
