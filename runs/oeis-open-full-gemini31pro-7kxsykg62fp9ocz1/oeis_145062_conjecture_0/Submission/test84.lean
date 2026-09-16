import Mathlib

noncomputable def A145062_aux : ℕ → ℕ → ℕ | _, _ => 1
noncomputable def a (n: ℕ) : ℕ := A145062_aux n 0
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 0 then 0 else a z.toNat

theorem test : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 0
  intro n
  have h : sequence_s_int (n + 0) = sequence_s_int n := by rw [add_zero]
  rw [h]
  unfold sequence_s_int
  have h2 : ¬((n:ℤ) < 0) := by omega
  simp [h2]
  have h3 : (n:ℤ).toNat = n := Int.toNat_natCast n
  rw [h3]
