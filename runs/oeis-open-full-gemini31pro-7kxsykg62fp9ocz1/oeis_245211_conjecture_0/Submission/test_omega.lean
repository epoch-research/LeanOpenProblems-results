import Mathlib

lemma mul_eq_5 {a b : ℕ} (h : a * b = 5) : (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1) := by
  have ha : a ≤ 5 := by
    have : a ∣ 5 := ⟨b, h.symm⟩
    exact Nat.le_of_dvd (by decide) this
  interval_cases a
  · norm_num at h
  · left; constructor; rfl; linarith
  · omega
  · omega
  · omega
  · right; constructor; rfl; linarith
