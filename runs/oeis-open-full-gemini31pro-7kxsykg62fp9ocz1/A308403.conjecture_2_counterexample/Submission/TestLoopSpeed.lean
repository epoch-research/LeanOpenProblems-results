import Mathlib

def fastLoop : Nat := Id.run do
  let mut count := 0
  for _ in [0:9000000000] do
    count := count + 1
  return count

theorem test : fastLoop = 9000000000 := by native_decide
