import Submission.Spec
import Mathlib.Data.ZMod.Basic

open A078590

theorem a078590_5_eq : A078590 5 = 171 := by rfl
theorem a078590_6_eq : A078590 6 = (2^171 + 1) / 9 := by rfl

theorem mod_18 : A078590 6 % 18 = 3 := by
  rw [a078590_6_eq]
  decide

lemma pow_mod (k : ℕ) : (2 : ZMod 19) ^ (18 * k + 3) = 8 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : 18 * (k + 1) + 3 = 18 * k + 3 + 18 := by omega
    rw [h, pow_add, ih]
    have h2 : (2 : ZMod 19) ^ 18 = 1 := by decide
    rw [h2, mul_one]

lemma val_mod_19 : (2 : ZMod 19) ^ A078590 6 = 8 := by
  have h1 : A078590 6 = 18 * (A078590 6 / 18) + (A078590 6 % 18) := by exact Eq.symm (Nat.div_add_mod (A078590 6) 18)
  rw [mod_18] at h1
  nth_rw 1 [h1]
  exact pow_mod (A078590 6 / 18)

lemma val_add_one_mod_19 : ((2 ^ A078590 6 + 1 : ℕ) : ZMod 19) = 9 := by
  push_cast
  rw [val_mod_19]
  rfl

lemma no_div_19 : ¬ 19 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  have h2 : ((2 ^ A078590 6 + 1 : ℕ) : ZMod 19) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (2 ^ A078590 6 + 1) 19).mpr h
  rw [val_add_one_mod_19] at h2
  revert h2
  decide

lemma no_div_171 : ¬ 171 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  have h19 : 19 ∣ 171 := by decide
  have h2 : 19 ∣ 2 ^ A078590 6 + 1 := dvd_trans h19 h
  exact no_div_19 h2

theorem disproof_thm : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  have h7 := h 7 (by decide)
  have h5 : A078590 (7 - 2) = 171 := by rfl
  have h6 : A078590 (7 - 1) = A078590 6 := by rfl
  rw [h5, h6] at h7
  exact no_div_171 h7

