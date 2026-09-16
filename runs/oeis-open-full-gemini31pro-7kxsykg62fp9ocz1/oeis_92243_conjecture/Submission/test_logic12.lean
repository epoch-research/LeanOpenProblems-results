import Submission.Spec
open Nat BigOperators Int

theorem generic_satisfies :
  ∃ f : ℕ → ℤ,
    (∃ n > 250000, f n > 0) ∧
    (∃ B, ∀ n, B ≤ f n) ∧
    (∃ B, ∀ n, f n ≤ B) ∧
    (Set.Infinite {n | f n > 0}) ∧
    (Set.Infinite {n | f n < 0}) := by
  use fun n => if Even n then (1 : ℤ) else (-1 : ℤ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · use 250002; refine ⟨by decide, ?_⟩
    have hE : Even 250002 := ⟨125001, rfl⟩
    simp [hE]
  · use -1; intro n
    by_cases h : Even n <;> simp [h]
  · use 1; intro n
    by_cases h : Even n <;> simp [h]
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    dsimp [upperBounds] at hM
    have hE : Even (M * 2 + 2) := ⟨M + 1, by omega⟩
    have h1 : M * 2 + 2 ∈ {n | (if Even n then (1:ℤ) else -1) > 0} := by simp [hE]
    have h2 : M * 2 + 2 ≤ M := hM h1
    omega
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    dsimp [upperBounds] at hM
    have hO : ¬ Even (M * 2 + 1) := by intro ⟨k, hk⟩; omega
    have h1 : M * 2 + 1 ∈ {n | (if Even n then (1:ℤ) else -1) < 0} := by simp [hO]
    have h2 : M * 2 + 1 ≤ M := hM h1
    omega
