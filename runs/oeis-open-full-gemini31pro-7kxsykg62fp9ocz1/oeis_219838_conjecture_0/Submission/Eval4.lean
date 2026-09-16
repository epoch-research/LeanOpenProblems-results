import Submission.Spec
import Mathlib

def check (n : ℕ) : Bool := a n == 0

#eval (List.range 2000).filter (fun n => n > 1 ∧ check n)
