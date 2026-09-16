import Submission.Spec

theorem t1 : (∀ n : ℕ, n > 2 ∧ n ≤ 10^6 → OeisA230507.A230507 n > 0) = (∀ n : ℕ, (n > 2 ∧ n ≤ 10^6) → OeisA230507.A230507 n > 0) := by rfl
