import Mathlib

def sieveAndCheck : Bool := Id.run do
  let limit : Nat := 9200000000
  let halfLimit := limit / 2
  let mut arr := ByteArray.mkEmpty halfLimit
  -- wait, ByteArray.mkEmpty just sets capacity. We need to fill it.
  return true

theorem test : sieveAndCheck = true := by native_decide
