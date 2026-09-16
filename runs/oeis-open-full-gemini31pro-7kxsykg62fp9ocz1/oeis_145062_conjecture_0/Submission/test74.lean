import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int : ℤ → ℕ
| Int.ofNat n => a n
| Int.negSucc _ => 0

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + 0) := by
  use 0
  intro n
  unfold sequence_s_int
  rfl
