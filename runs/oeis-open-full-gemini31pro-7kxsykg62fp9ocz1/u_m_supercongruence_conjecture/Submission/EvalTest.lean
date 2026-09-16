import Submission.Spec
open Nat Finset

def u_comp (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      ((n + 2 * k).choose k) * n / (n + 2 * k)

#eval u_comp 1 5
#eval u_comp 1 1
