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
  · use 250002; decide
  · use -1; intro n; split <;> decide
  · use 1; intro n; split <;> decide
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have : (M * 2 + 2) ∈ {n | (if Even n then 1 else -1) > (0:ℤ)} := by
      simp [Even, even_add, even_two]
    have := hM this
    omega
  · apply Set.infinite_of_not_bddAbove
    intro ⟨M, hM⟩
    have : (M * 2 + 1) ∈ {n | (if Even n then 1 else -1) < (0:ℤ)} := by
      simp; sorry
