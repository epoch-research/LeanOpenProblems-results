import Mathlib

def testSum : Nat :=
  let n := 4551086841
  (Finset.range (n + 1)).sum fun i =>
    if i < 10 then 1 else 0

theorem test : testSum = 10 := by native_decide
