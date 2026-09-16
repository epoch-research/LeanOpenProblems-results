import Submission.Spec
open Nat Finset

def A264010_comp (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Bool := decide (k.Prime ∨ (k + 1).Prime)
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

#eval! (List.range 30).map fun n => (n, A264010_comp n)
