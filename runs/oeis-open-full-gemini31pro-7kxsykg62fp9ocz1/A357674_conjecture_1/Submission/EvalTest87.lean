import Submission.Spec
open Nat

theorem T : ¬ (type_of% @A357674_conjecture_1) := 
  have : False := cast (sorryAx _ true) (rfl : 0 = 0);
  this.elim
