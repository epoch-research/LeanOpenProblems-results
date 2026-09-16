import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def a (n: ℕ) : ℕ := sequence_s_int n

theorem my_proof : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 0
  intro n
  change a n = sequence_s_int (n + (0:ℤ))
  rw [add_zero]
  change sequence_s_int (n) = sequence_s_int (n:ℤ)
  rfl
#print axioms my_proof
