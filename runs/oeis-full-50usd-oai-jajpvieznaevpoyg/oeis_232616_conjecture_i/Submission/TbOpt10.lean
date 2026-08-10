import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def noOddDiv (n d fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 =>
      if n < d*d then true
      else if n % d == 0 then false
      else noOddDiv n (d+2) fuel

def isPrimeFast (n : Nat) : Bool :=
  if n = 2 then true else
  if n < 2 then false else
  if n % 2 = 0 then false else
  noOddDiv n 3 ((n+1)/2)

def countBlockF : Nat → Nat → Nat
  | 0, lo => if isPrimeFast lo then 1 else 0
  | d+1, lo => countBlockF d lo + countBlockF d (lo + 2^d)

#eval countBlockF 10 8160000

theorem fb10 : countBlockF 10 8160000 = 66 := rfl
#print axioms fb10
