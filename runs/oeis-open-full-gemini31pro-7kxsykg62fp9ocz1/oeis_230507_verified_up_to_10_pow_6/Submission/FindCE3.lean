import Submission.Spec
open OeisA230507

def isPrimeLoop (n i : Nat) : Bool :=
  if h : i * i > n then true
  else if n % i == 0 then false
  else isPrimeLoop n (i + 1)
termination_by n - i
decreasing_by sorry

def isPrimeFast (n : Nat) : Bool :=
  if n < 2 then false else isPrimeLoop n 2

def P2_fast (m : Nat) : Bool :=
  m > 0 && isPrimeFast (2 * m + 1) && isPrimeFast (2 * m^4 - 1)

def Z_fast (m : Nat) : Bool :=
  m > 0 && isPrimeFast (2 * m - 1) && isPrimeFast (2 * m^4 - 1)

def check2 (n : Nat) : Bool :=
  Id.run do
    for x in [1:n] do
      for y in [1:n-x] do
        let z := n - x - y
        if P2_fast x && P2_fast y && Z_fast z then
          return true
    return false

def findCE : Nat :=
  Id.run do
    for n in [9:1000] do
      if not (check2 n) then
        return n
    return 0

#eval! findCE
