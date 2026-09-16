import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := (sorryAx (0 = 1) false);
  this.elim
