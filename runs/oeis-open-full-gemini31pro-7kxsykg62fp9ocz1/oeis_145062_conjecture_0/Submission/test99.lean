import Mathlib

noncomputable def A145062_aux : ℕ → ℕ → ℕ | _, _ => 1
noncomputable def a (n: ℕ) : ℕ := A145062_aux n 0
noncomputable def sequence_s_int (z : ℤ) : ℕ := 0

theorem foo : ¬ (∀ n : ℕ, a n = sequence_s_int (n + 0)) := by
  intro hk
  have h := hk 0
  change 1 = sequence_s_int (0 + 0) at h
  unfold sequence_s_int at h
  contradiction
