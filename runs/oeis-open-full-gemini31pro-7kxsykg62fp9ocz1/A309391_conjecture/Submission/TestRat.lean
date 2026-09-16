import Submission.Spec

def H_exact (n : ℕ) : ℚ := Id.run do
  let mut acc : ℚ := 0
  for i in [1:n+1] do
    acc := acc + (1 : ℚ) / (i : ℚ)
  return acc

#eval (H_exact 20000).num > 0
