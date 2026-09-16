import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    Id.run do
      let mut i := 2
      let mut is_p := true
      while i * i <= n do
        if n % i == 0 then
          is_p := false
          break
        i := i + 1
      is_p

def countPrimes (limit : ℕ) : ℕ := Id.run do
  let mut count := 0
  for i in [2:limit] do
    if isPrime i then
      count := count + 1
  return count

theorem test : countPrimes 1000000 = 78498 := by native_decide
