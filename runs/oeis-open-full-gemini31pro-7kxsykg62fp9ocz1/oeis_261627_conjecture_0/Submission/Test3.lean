import Submission.Spec
open Nat Finset

def conjecture_stmt (n : ℕ) : Prop :=
  (n > 6 → A261627 n > 0) ∧
  (A261627 n = 1 ↔ n ∈ A261627_singletons)

theorem check_7 : conjecture_stmt 7 := by sorry
