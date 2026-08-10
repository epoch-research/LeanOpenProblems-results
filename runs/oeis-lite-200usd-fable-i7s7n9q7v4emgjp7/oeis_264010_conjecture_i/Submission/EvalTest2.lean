import FormalConjectures.Util.ProblemImports
open Nat Finset
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0
#eval A264010 211
#eval A264010 305
