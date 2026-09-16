import Submission.Spec
open Nat Finset

def A264010_comp (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Bool := decide (k.Prime ∨ (k + 1).Prime)
  let maxX := n.sqrt
  (range (maxX + 1)).sum fun x =>
    let rem1 := n - x * x
    let maxY := rem1.sqrt
    (range (maxY + 1)).sum fun y =>
      if rem1 < y * (y + 1) then 0 else
      let rem2 := rem1 - y * (y + 1)
      let maxZ := (2 * rem2).sqrt
      (range (maxZ + 1)).sum fun z =>
        if rem2 == T z ∧ prime_cond y ∧ prime_cond z then 1 else 0

#eval! A264010_comp 1125
