import Mathlib

open Finset Nat

def count_reps (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

#eval count_reps 331269
