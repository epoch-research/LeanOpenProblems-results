import Submission.Spec
open Nat Finset

def fast_check (n : Nat) : Nat := Id.run do
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Bool := decide (k.Prime ∨ (k + 1).Prime)
  let mut c := 0
  let maxX := n.sqrt
  for x in [0:maxX+1] do
    let rem1 := n - x * x
    let maxY := rem1.sqrt
    for y in [0:maxY+1] do
      if y * (y + 1) ≤ rem1 then
        let rem2 := rem1 - y * (y + 1)
        let maxZ := (2 * rem2).sqrt
        for z in [0:maxZ+1] do
          if T z == rem2 ∧ prime_cond y ∧ prime_cond z then
            c := c + 1
  return c

#eval! fast_check 1126
