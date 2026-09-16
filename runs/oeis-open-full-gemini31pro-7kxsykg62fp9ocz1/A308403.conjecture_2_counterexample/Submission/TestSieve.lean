import Mathlib

def mySieve (limit : Nat) : Nat := Id.run do
  let half := limit / 2
  let mut arr := Array.mkArray half true
  arr := arr.set! 0 false
  let mut i := 1
  while 2 * i * (i + 1) < half do
    if arr.get! i then
      let p := 2 * i + 1
      let mut j := 2 * i * (i + 1)
      while j < half do
        arr := arr.set! j false
        j := j + p
    i := i + 1
  let mut count := 1
  for k in [1:half] do
    if arr.get! k then count := count + 1
  return count

theorem test : mySieve 10000000 = 664579 := by native_decide
