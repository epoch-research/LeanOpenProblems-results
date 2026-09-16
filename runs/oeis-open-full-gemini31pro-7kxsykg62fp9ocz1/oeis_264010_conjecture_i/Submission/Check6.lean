import Submission.Spec
open Nat Finset

def A264010_comp (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Bool := k.decidablePrime
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if x * x + y * (y + 1) + T z = n ∧ (prime_cond y ∨ prime_cond (y + 1)) ∧ (prime_cond z ∨ prime_cond (z + 1)) then 1 else 0

#eval A264010_comp 3
