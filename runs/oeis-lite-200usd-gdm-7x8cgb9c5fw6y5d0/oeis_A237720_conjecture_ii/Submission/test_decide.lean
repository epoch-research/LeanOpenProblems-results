import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt.iter

lemma group0 : ∀ n < 1003, 3 ≤ n → ∃ p < n, p.Prime ∧ (sqrt (n + p)).Prime := by
  decide

lemma group1 : ∀ n < 203, 103 ≤ n → ∃ p < n, p.Prime ∧ (sqrt (n + p)).Prime := by
  decide

theorem test_combine (n : ℕ) (hn : 3 ≤ n) (hn2 : n < 203) : ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  by_cases h0 : n < 103
  · obtain ⟨p, hp_lt, hp_prime, hsqrt_prime⟩ := group0 n h0 hn
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have hn_ge : 103 ≤ n := by omega
    obtain ⟨p, hp_lt, hp_prime, hsqrt_prime⟩ := group1 n hn2 hn_ge
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩

















