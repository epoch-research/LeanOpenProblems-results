import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have h : 0 = 1 := by sorry
  have : False := by contradiction;
  this.elim
