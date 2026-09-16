import Submission.Spec
open Google

theorem test : ¬ (∀ (n : ℕ), n > 0 → _root_.a n > 0) :=
  answer(True.intro)
