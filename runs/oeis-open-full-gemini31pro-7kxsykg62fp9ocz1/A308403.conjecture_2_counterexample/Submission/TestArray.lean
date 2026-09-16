import Mathlib

def testArray : Nat := Id.run do
  let limit := 575000000
  let arr := mkArray limit (1 : UInt8)
  return arr.size

theorem test : testArray = 575000000 := by native_decide
