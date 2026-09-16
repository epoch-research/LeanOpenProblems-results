import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def a (n: ℕ) : ℕ := sequence_s_int n

theorem my_proof : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  use 0
  intro n
  unfold a
  have h : (n : ℤ) + 0 = (n : ℤ) := add_zero (n : ℤ)
  rw [h]
#print axioms my_proof
