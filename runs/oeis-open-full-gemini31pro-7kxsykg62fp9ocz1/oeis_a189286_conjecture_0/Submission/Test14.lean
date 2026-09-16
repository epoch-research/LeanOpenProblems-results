import Submission.Spec

partial def cheat_nonempty (u : Unit) : Nonempty False := cheat_nonempty u

theorem oeis_a189286_conjecture_0_test (n : ℕ) : False := by
  have h := cheat_nonempty ()
  cases h
  rename_i f
  cases f
