import Mathlib.Data.ZMod.Basic

def square_loop (x : ℕ) (n : ℕ) : ℕ := Id.run do
  let mut acc := x
  for _ in [0:n] do
    acc := (acc * acc) % 1000000
  return acc

theorem test_loop : square_loop 2 30000 = 612544 := by
  decide
