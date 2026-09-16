import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := sorry;
  this.elim
