import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def aa (n : ℕ) : ℕ := by
  classical
  exact if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else if n = 0 then 0 else 2

theorem proto (n : ℕ) (hn : n ≥ 1) : aa n > 0 ∧ (Odd (aa n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  classical
  by_cases h : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
  · simp [aa, h]
  · have hn0 : n ≠ 0 := by omega
    simp [aa, h, hn0]
