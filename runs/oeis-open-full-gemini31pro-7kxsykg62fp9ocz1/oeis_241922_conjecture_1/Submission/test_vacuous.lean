import Submission.Spec

lemma not_vacuous : ∃ n : ℕ, Even n ∧ n > 2 := by
  use 4
  decide
