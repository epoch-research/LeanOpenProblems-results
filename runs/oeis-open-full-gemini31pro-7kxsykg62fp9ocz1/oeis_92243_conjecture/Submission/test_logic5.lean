import Submission.Spec
open Nat BigOperators Int

theorem generic_satisfies :
  ∃ f : ℕ → ℤ,
    (∃ n > 250000, f n > 0) ∧
    (∃ B, ∀ n, B ≤ f n) ∧
    (∃ B, ∀ n, f n ≤ B) ∧
    (Set.Infinite {n | f n > 0}) ∧
    (Set.Infinite {n | f n < 0}) := by
  use fun n => if Even n then 1 else -1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · use 250002; refine ⟨by decide, ?_⟩
    simp [Even]
  · use -1; intro n; by_cases h : Even n <;> simp [h]
  · use 1; intro n; by_cases h : Even n <;> simp [h]
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have h1 : M * 2 ∈ {n | (if Even n then 1 else -1) > (0:ℤ)} := by
      simp; left; use M
    have := hM h1
    omega
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have h1 : M * 2 + 1 ∈ {n | (if Even n then 1 else -1) < (0:ℤ)} := by
      simp; intro x; omega
    have := hM h1
    omega
