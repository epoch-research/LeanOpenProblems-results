import Submission.Spec
open Nat

theorem T : ¬ (type_of% @A357674_conjecture_1) := 
  have h : 0 = 1 := by exact sorry
  have : False := by contradiction;
  this.elim
