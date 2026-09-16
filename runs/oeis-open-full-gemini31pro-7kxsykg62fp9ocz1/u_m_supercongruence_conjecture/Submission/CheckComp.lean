import Submission.Spec
open Nat Finset

def u_comp2 (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat

#eval (u_comp2 1 10) % 125
#eval (u_comp2 1 2) % 125
