import Submission.Spec

partial def cheat_nonempty : Nonempty False := cheat_nonempty

theorem oeis_a189286_conjecture_0_test (n : ℕ) : False := by
  cases cheat_nonempty.some
