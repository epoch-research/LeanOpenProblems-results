import Mathlib

open Nat

theorem test : ∃ n, n = 10 := by
  exact ⟨10, rfl⟩

#print axioms test
