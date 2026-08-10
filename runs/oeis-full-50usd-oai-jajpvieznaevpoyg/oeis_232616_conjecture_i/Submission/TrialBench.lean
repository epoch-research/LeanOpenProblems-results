import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def noDivUpTo (n d fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 =>
      if d*d > n then true
      else if n % d == 0 then false
      else noDivUpTo n (d+1) fuel

def isPrimeTrial (n : Nat) : Bool := 2 <= n && noDivUpTo n 2 n

def countBlockT : Nat → Nat → Nat
  | 0, lo => if isPrimeTrial lo then 1 else 0
  | d+1, lo => countBlockT d lo + countBlockT d (lo + 2^d)

#eval countBlockT 12 0

theorem tb12 : countBlockT 12 0 = 564 := by decide

theorem tb12hi : countBlockT 12 8160000 = 262 := by decide
#print axioms tb12hi

#print axioms tb12
