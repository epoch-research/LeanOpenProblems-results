import Submission.Spec
open Padic

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem test_div : ((-25 : ℤ) : Padic 5) / ((25 : ℕ) : Padic 5) = (-1 : Padic 5) := by
  sorry
