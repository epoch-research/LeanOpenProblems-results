import Mathlib

def fastLoop (limit : Nat) : Nat := Id.run do
  let mut count := 0
  for i in [0:limit] do
    count := count + 1
  return count

theorem test : fastLoop 400000000 = 400000000 := by native_decide
