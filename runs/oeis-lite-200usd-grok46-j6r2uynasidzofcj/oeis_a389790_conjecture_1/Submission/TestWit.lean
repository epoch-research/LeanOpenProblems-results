import FormalConjectures.Util.ProblemImports
open Classical
open Nat

def trialDiv (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.blt n (d * d) then true
    else if n % d == 0 then false
    else trialDiv n (d + 1) fuel

def isPrimeBool (n : ℕ) : Bool :=
  if Nat.blt n 2 then false else trialDiv n 2 n

def nextPrimeGo (k : ℕ) : ℕ → ℕ
  | 0 => k
  | f + 1 => if isPrimeBool k then k else nextPrimeGo (k + 1) f

def nextPrimeFuel (n fuel : ℕ) : ℕ := nextPrimeGo (n + 1) fuel
def nextPrimeComp (n : ℕ) : ℕ := nextPrimeFuel n (n + 3)

def checkPair (n p q : ℕ) : Bool :=
  isPrimeBool p && isPrimeBool q && Nat.ble p q && Nat.blt p n && Nat.blt q n &&
    (p + nextPrimeComp p + q + nextPrimeComp q == 2 * n)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem c474 : checkPair 474 7 463 = true := rfl
theorem c511 : checkPair 511 157 349 = true := rfl
theorem c16000 : checkPair 16000 179 15817 = true := rfl
theorem c100000 : checkPair 100000 31 99961 = true := rfl
