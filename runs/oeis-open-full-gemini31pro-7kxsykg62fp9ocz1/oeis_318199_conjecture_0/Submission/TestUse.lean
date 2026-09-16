import Mathlib

def A318199 (n : ℕ) : ℕ := n

theorem oeis_318199_conjecture_0 :
  ¬ ∃ (N : ℕ) (hN : 0 < N),
    ∀ (i : ℕ), i < 17 → A318199 (N + i) < A318199 (N + i + 1) := by sorry

theorem disproof : ¬ (type_of% @oeis_318199_conjecture_0) := by
  intro h
  have h_ex : ∃ (N : ℕ) (hN : 0 < N), ∀ (i : ℕ), i < 17 → A318199 (N + i) < A318199 (N + i + 1) := by
    use 1
    use Nat.zero_lt_one
    intro i _
    exact Nat.lt_succ_self (1 + i)
  exact h h_ex
