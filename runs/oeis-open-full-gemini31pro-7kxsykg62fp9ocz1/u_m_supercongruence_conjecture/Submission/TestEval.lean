import Submission.Spec
open Nat

def u_comp (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (Finset.range (m * n + 1)).sum fun k : ℕ =>
      (n * (n + 2 * k).choose k) / (n + 2 * k)

theorem u_eq_u_comp (m n : ℕ) : u m n = u_comp m n := by
  sorry
