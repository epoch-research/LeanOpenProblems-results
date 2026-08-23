import FormalConjectures.Util.ProblemImports

open Nat

def hasOddDivR (n lo hi : ℕ) : Bool :=
  if hi ≤ lo then false
  else if hi = lo + 1 then
    let d := 2 * lo + 3
    d * d ≤ n && n % d == 0
  else
    let mid := (lo + hi) / 2
    hasOddDivR n lo mid || hasOddDivR n mid hi
termination_by hi - lo

def isPrimeB : ℕ → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true
  | n + 4 =>
      let m := n + 4
      (m % 2 != 0) && (m % 3 != 0) && !(hasOddDivR m 0 m)

def countR (n lo hi : ℕ) : ℕ :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then
    let q := lo
    if 5 ≤ q && isPrimeB q && isPrimeB (n - q) && isPrimeB (n + q) then 1 else 0
  else
    let mid := (lo + hi) / 2
    let left := countR n lo mid
    if 5 ≤ left then left else left + countR n mid hi
termination_by hi - lo

def aB5 (n : ℕ) : ℕ :=
  let c := countR n 5 n
  if 5 ≤ c then 5 else c

def checkK : ℕ → Bool
  | 0 => true
  | k + 1 =>
      let n := 6 * (k + 4)
      (5 ≤ aB5 n) && checkK k

set_option maxRecDepth 20000000
set_option maxHeartbeats 0

#eval aB5 24
#eval aB5 48
#eval aB5 192
#eval checkK 80
#eval isPrimeB 5
#eval isPrimeB 17
#eval isPrimeB 19
#eval isPrimeB 29
