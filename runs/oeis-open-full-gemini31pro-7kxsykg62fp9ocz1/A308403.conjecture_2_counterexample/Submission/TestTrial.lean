import Mathlib

def isPrimeComp (n : UInt32) : Bool :=
  if n < 2 then false
  else if n % 2 == 0 then n == 2
  else if n % 3 == 0 then n == 3
  else Id.run do
    let mut i : UInt32 := 5
    while i * i <= n do
      if n % i == 0 || n % (i + 2) == 0 then return false
      i := i + 6
    return true

def countPrimes (limit : UInt32) : Nat := Id.run do
  let mut count := 0
  for i in [0:limit.toNat] do
    if isPrimeComp i.toUInt32 then
      count := count + 1
  return count

theorem test : countPrimes 10000000 = 664579 := by native_decide
