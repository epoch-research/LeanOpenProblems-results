import Mathlib.Data.ZMod.Basic

open Nat

theorem natCast_ne_zero_of_lt {M : ℕ} (hM : 3 < M) : ((3 : ℕ) : ZMod M) ≠ 0 := by
  intro h
  have h_val := congr_arg ZMod.val h
  rw [ZMod.val_natCast M 3, ZMod.val_zero] at h_val
  rw [Nat.mod_eq_of_lt hM] at h_val
  contradiction

theorem test_ineq_21 : 3 < 10 ^ (2 ^ 21) + 1 := by
  have h1 : 3 < 10 ^ 1 + 1 := by decide
  apply lt_of_lt_of_le h1
  apply Nat.add_le_add_right
  apply Nat.pow_le_pow_right (by decide)
  have h2 : 1 ≤ 2 ^ 21 := by decide
  exact h2


