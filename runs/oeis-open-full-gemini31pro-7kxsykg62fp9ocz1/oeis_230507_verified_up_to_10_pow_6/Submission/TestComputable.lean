import Submission.Spec
open OeisA230507

instance {m : ℕ} : Decidable (S_condition m) :=
  instDecidableAnd

theorem t3 : A230507 3 = 1 := by decide
