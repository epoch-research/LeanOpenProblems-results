import Mathlib

set_option maxHeartbeats 0

def test_loop : ℕ := Id.run do
  let mut acc := 0
  for i in [1:100000000] do
    acc := acc + i % 3
  return acc

def test : test_loop > 0 := by native_decide
