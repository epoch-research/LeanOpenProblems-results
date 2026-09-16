import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def a (n: ℕ) : ℕ := n

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  first
  | (use 0; intro n; unfold sequence_s_int; rfl; done)
  | sorry
