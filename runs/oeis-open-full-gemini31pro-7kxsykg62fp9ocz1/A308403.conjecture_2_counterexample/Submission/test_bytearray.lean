import Mathlib

def testByteArray (n : ℕ) : ℕ :=
  let arr := ByteArray.mkEmpty n
  let arr := arr.push 1
  let arr := arr.push 2
  (arr.get! 0).toNat + (arr.get! 1).toNat

theorem test_ba : testByteArray 10 = 3 := by native_decide
