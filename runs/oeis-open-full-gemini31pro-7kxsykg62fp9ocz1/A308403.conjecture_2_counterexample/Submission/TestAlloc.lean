import Mathlib

def testAlloc : Bool := Id.run do
  let limit : USize := 9000000000
  let mut arr := ByteArray.mkEmpty limit.toNat
  return true

theorem test : testAlloc = true := by native_decide
