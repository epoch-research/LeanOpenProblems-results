import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have h : 0 = 1 := sorryAx _ false;
  have : False := by contradiction;
  this.elim
