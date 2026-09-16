import Mathlib

def testAlloc : Nat := Id.run do
  let limit := 4500000000
  let arr := Array.mkArray limit (1 : UInt8)
  return 1

theorem test : testAlloc = 1 := by native_decide
