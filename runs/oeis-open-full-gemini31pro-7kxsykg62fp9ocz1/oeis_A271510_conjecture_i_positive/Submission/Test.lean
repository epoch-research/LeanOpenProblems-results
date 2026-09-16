import Submission.Spec

def find_counterexample_loop (curr max : ℕ) : Option ℕ :=
  if curr > max then none
  else if _root_.A271510 curr == 0 then some curr
  else find_counterexample_loop (curr + 1) max
termination_by max - curr

#eval! find_counterexample_loop 0 2000
