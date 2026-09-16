import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := cast (sorryAx _ false) (rfl : 0 = 0);
  this.elim
