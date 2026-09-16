import Mathlib

partial def minFacAux_UInt64 (n : UInt64) (k : UInt64) : UInt64 :=
  if n < k * k then n
  else if n % k == 0 then k
  else minFacAux_UInt64 n (k + 2)

def isPrime_UInt64 (n : UInt64) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else minFacAux_UInt64 n 3 == n

def fast_a (n : UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for s in [1:n.toNat] do
    let s64 := UInt64.ofNat s
    let p := n * n + s64 * s64
    if isPrime_UInt64 p then
      acc := acc + 1
  return acc

def fast_pi (n : UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for s in [2:n.toNat] do
    let s64 := UInt64.ofNat s
    if isPrime_UInt64 s64 then
      acc := acc + 1
  return acc

#eval fast_pi 512720
#eval fast_a 512720
