import FormalConjectures.Util.ProblemImports

open Nat

set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt
attribute [local reducible] Nat.sqrt.iter

theorem test (n : ℕ) (hn : n ≥ 3) (hn2 : n ≤ 12) : ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  interval_cases n
  · have : ∃ p < 3, p.Prime ∧ (sqrt (3 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 4, p.Prime ∧ (sqrt (4 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 5, p.Prime ∧ (sqrt (5 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 6, p.Prime ∧ (sqrt (6 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 7, p.Prime ∧ (sqrt (7 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 8, p.Prime ∧ (sqrt (8 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 9, p.Prime ∧ (sqrt (9 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 10, p.Prime ∧ (sqrt (10 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 11, p.Prime ∧ (sqrt (11 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
  · have : ∃ p < 12, p.Prime ∧ (sqrt (12 + p)).Prime := by decide
    rcases this with ⟨p, hp_lt, hp_prime, hsqrt_prime⟩
    exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
