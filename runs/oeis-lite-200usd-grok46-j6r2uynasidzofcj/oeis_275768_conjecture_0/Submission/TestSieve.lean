import FormalConjectures.Util.ProblemImports

open Nat

def hasDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    (d * d ≤ n && n % d == 0) || hasDiv n fuel (d + 1)

def isPrimeB : ℕ → Bool
  | 0 => false
  | 1 => false
  | n + 2 => !(hasDiv (n + 2) (n + 2) 2)

def aGo (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 =>
    let rest := aGo n q
    if q ≥ 3 && q < n && isPrimeB q && isPrimeB (n - q) && isPrimeB (n + q) then
      rest + 1
    else rest

def aB (n : ℕ) : ℕ := aGo n n

def checkFrom24 : ℕ → Bool
  | 0 => true
  | k + 1 =>
    let n := 6 * (k + 4)
    (aB n != 4) && checkFrom24 k

set_option maxRecDepth 20000000
set_option maxHeartbeats 0

example : checkFrom24 40 = true := by rfl
