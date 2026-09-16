import Submission.Spec

def fast_check : Nat := Id.run do
  let n := 33
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Bool := decide (k.Prime ∨ (k + 1).Prime)
  let mut c := 0
  for x in [0:n+1] do
    for y in [0:n+1] do
      for z in [0:n+1] do
        if x * x + y * (y + 1) + T z == n ∧ prime_cond y ∧ prime_cond z then
          c := c + 1
  return c

#eval! fast_check
