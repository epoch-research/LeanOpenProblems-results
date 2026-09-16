import Submission.Spec

def check (n : ℕ) : Bool :=
  if n == 0 then true
  else (A179537_sum_weighted n) % n == 0

#eval (List.range 1000).all check
