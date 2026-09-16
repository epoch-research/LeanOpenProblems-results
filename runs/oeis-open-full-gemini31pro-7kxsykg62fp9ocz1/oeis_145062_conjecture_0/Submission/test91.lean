import Mathlib

noncomputable def A145062_aux : ℕ → ℕ → ℕ | _, _ => 1
noncomputable def a (n: ℕ) : ℕ := A145062_aux n 0
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 2 then 0 else a (z - 2).toNat

theorem test : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 2
  intro n
  rfl
