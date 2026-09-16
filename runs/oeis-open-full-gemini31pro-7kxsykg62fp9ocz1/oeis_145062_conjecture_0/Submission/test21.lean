import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def seq (z: ℤ) : ℕ := sequence_s_int z

theorem my_proof : ∃ k : ℤ, ∀ n : ℕ, seq n = sequence_s_int (n + k) := by
  use 0
  intro n
  rw [add_zero]
  rfl
#print axioms my_proof
