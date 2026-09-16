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

def S_cond_fast (m : Nat) : Bool :=
  isPrimeFast (2 * m + 1) && isPrimeFast (2 * m^3 + 1)

def A230507_fast (n : Nat) : Nat :=
  Id.run do
    let mut c := 0
    for a in [1 : n / 3 + 1] do
      for b in [a : (n - a) / 2 + 1] do
        let cc := n - a - b
        if S_cond_fast a && S_cond_fast b && S_cond_fast cc then
          c := c + 1
    return c

def findCE1 : Nat :=
  Id.run do
    for n in [3:100] do
      if A230507_fast n == 0 then
        return n
    return 0

#eval! findCE1
