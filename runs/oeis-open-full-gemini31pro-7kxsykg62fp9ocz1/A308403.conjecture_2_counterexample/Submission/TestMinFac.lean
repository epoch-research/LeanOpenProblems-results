import Mathlib

def countPrimesMinFac (limit : ℕ) : ℕ := Id.run do
  let mut count := 0
  for i in [2:limit] do
    if Nat.minFac i == i then
      count := count + 1
  return count

theorem test : countPrimesMinFac 1000000 = 78498 := by native_decide
