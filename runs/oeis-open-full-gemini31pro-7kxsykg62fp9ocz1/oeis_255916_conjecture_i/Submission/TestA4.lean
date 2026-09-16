import Submission.Spec
open Nat Int

def g (k : ℤ) : ℕ := ((5 * k^2 - 3 * k) / 2).toNat
def p8 (x : ℕ) : ℕ := x * (3 * x - 2)
def p9 (y : ℕ) : ℕ := y * (7 * y - 5) / 2

def check_rep (n : ℕ) : Bool :=
  let bound := n + 1
  Id.run do
    for k_idx in [0 : 2 * bound + 1] do
      let k : ℤ := (k_idx : ℤ) - (bound : ℤ)
      for x in [0 : bound] do
        for y in [0 : bound] do
          if g k + p8 x + p9 y == n then
            return true
    return false

#eval check_rep 0
#eval check_rep 1
#eval check_rep 2
#eval check_rep 3
#eval check_rep 4
