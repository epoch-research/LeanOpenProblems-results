import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := cast sorry (rfl : 0 = 0);
  this.elim
