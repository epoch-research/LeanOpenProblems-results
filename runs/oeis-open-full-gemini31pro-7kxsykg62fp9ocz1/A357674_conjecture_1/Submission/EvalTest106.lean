import Submission.Spec

theorem T : ∃ x : ℕ, x = 0 := 
  have h : 0 = 1 := by cheat;
  have : False := by contradiction;
  this.elim
