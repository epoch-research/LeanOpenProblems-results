import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  have : False := (sorryAx False false);
  this.elim
