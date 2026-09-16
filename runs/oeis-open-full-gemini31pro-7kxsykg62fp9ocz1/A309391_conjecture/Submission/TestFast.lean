import Mathlib.Data.Nat.Basic

def fast_loop (n : ℕ) : ℕ := Id.run do
  let mut acc : ℕ := 0
  for i in [0:n] do
    acc := acc + i
  return acc

#eval fast_loop 283686649
