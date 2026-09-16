import Mathlib

open Finset Nat

def A352286 (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

def A352286_exceptions : Set ℕ := {106, 744, 5469, 331269}

#eval A352286 106
#eval A352286 744
#eval A352286 5469
