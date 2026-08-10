import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def fastPrime (n : ℕ) : Bool := @decide (Nat.Prime n) (Nat.decidablePrime' n)

def nthPrimeLoop : ℕ → ℕ → ℕ → ℕ
  | 0, k, n => n-1
  | fuel+1, k, n => if fastPrime n then if k=0 then n else nthPrimeLoop fuel (k-1) (n+1) else nthPrimeLoop fuel k (n+1)

def nthPrimeFast (k : ℕ) : ℕ := nthPrimeLoop (20*k+100) k 0
#eval nthPrimeFast 10
example : nthPrimeFast 664579 = 10000019 := by native_decide
