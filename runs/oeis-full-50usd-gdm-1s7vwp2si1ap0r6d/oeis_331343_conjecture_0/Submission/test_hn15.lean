import FormalConjectures.Util.ProblemImports

open Nat

lemma n_ge_15 (n : ℕ) (hn : n > 3) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) (hn9 : n ≠ 9) : n ≥ 15 := by
  by_contra h_lt
  have h_le : n ≤ 14 := by omega
  have h_cases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 := by
    have : n % 2 = 1 := h_odd
    omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- n = 1
    -- but n > 3
    omega
  · -- n = 3
    -- but n > 3
    omega
  · -- n = 5
    have : Nat.Prime 5 := by decide
    contradiction
  · -- n = 7
    have : Nat.Prime 7 := by decide
    contradiction
  · -- n = 9
    contradiction
  · -- n = 11
    have : Nat.Prime 11 := by decide
    contradiction
  · -- n = 13
    have : Nat.Prime 13 := by decide
    contradiction
