import Submission.Spec
open PowerSeries

theorem test : ∃ (x : PQS), x = A097913.generating_function := by
  exact ⟨A097913.generating_function, rfl⟩
