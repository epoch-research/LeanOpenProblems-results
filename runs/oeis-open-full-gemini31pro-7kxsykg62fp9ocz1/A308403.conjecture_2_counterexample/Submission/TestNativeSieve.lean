import Mathlib

def sieve (limit : Nat) : Nat := Id.run do
  let mut arr := ByteArray.empty
  for _ in [0:limit] do
    arr := arr.push 1
  let mut count := 0
  for p in [2:limit] do
    if arr.get! p == 1 then
      count := count + 1
      let mut multiple := p * p
      while multiple < limit do
        arr := arr.set! multiple 0
        multiple := multiple + p
  return count

theorem test : sieve 10000000 = 664579 := by native_decide
