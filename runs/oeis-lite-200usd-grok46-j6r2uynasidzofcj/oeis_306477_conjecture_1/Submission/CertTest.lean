import FormalConjectures.Util.ProblemImports

open Nat

def isSq (t : ℕ) : ℕ :=
  if sqrt t * sqrt t = t then 1 else 0

def isOddSq (t : ℕ) : ℕ :=
  if sqrt t * sqrt t = t && (sqrt t) % 2 = 1 then 1 else 0

-- 8*6+1 = 49 = 7^2, odd square (6 is triangular)
example : isOddSq (8 * 6 + 1) = 1 := by decide

-- 8*7+1 = 57 not square
example : isOddSq (8 * 7 + 1) = 0 := by decide

def noTriQ (n : ℕ) : ℕ → ℕ
  | 0 =>
      isOddSq (8 * n + 1) -- x=0, Q=0
  | x + 1 =>
      let q := (x + 1 + 3).choose 4
      let bit := if q ≤ n then isOddSq (8 * (n - q) + 1) else 0
      bit + noTriQ n x

-- n=10, Q values 0,1,5,15>10. 10,9,5 none triangular? 
-- T: 1,3,6,10. 10 is T! so should be 1
example : noTriQ 10 5 = 1 := by decide

-- n=2: 2-0=2 not T, 2-1=1 is T. so 1
example : noTriQ 2 5 = 1 := by decide

-- A number that's not TQ with small x: let's just test reduction speed
set_option maxHeartbeats 20000000

-- 200 values of x for n = 10^6+17
example : noTriQ 1000017 200 > 0 := by decide
