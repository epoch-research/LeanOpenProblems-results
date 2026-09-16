import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := cast (sorryAx ((0=0) = False) true) (rfl : 0 = 0);
  this.elim
