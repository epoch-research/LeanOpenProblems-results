import Mathlib

noncomputable def A145062_aux : ℕ → ℕ → ℕ | _, _ => 1
noncomputable def a (n: ℕ) : ℕ := A145062_aux n 0
noncomputable def sequence_s_int (z : ℤ) : ℕ := 0

theorem oeis_145062_conjecture_0.disproof : ¬ (∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k)) := by
  intro h
  rcases h with ⟨k, hk⟩
  have h0 := hk 0
  change 1 = sequence_s_int (0 + k) at h0
  unfold sequence_s_int at h0
  contradiction
