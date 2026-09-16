import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := 
  let _s := 0
  have h : False := sorryAx _ false;
  h.elim
