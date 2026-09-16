import Submission.Spec

theorem generic_satisfies :
  ∃ f : ℕ → ℤ,
    (∃ n > 250000, f n > 0) ∧
    (∃ B, ∀ n, B ≤ f n) ∧
    (∃ B, ∀ n, f n ≤ B) ∧
    (Set.Infinite {n | f n > 0}) ∧
    (Set.Infinite {n | f n < 0}) := by
  use fun n => if Even n then 1 else -1
  sorry
