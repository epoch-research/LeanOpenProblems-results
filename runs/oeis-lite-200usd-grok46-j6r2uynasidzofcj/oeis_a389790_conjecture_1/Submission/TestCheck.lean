import FormalConjectures.Util.ProblemImports
open Classical
open Nat

-- Minimal copy of the computational engine to test checkFrom scale.
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

def primesUpTo (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun k => isPrimeBool k)

def consecutiveSums : List ℕ → List ℕ
  | p :: p' :: rest => (p + p') :: consecutiveSums (p' :: rest)
  | _ => []

def ssumList (n : ℕ) : List ℕ :=
  let ps := primesUpTo n
  match ps.getLast? with
  | none => []
  | some lastP =>
    let inner := consecutiveSums ps
    let nxt := nextPrimeComp lastP
    if Nat.blt n nxt then inner ++ [lastP + nxt] else inner

def listHas (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => if x == y then true else listHas x ys

def listHasPair (n : ℕ) (ss : List ℕ) : List ℕ → Bool
  | [] => false
  | s :: rest =>
    if Nat.ble s n && listHas (2 * n - s) ss then true
    else listHasPair n ss rest

def hasRepFast (n : ℕ) : Bool :=
  let ss := ssumList n
  listHasPair n ss ss

def checkFrom (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => hasRepFast (lo + n) && checkFrom lo n

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem t824 : checkFrom 824 5 = true := rfl
theorem t824_20 : checkFrom 824 20 = true := rfl
theorem t900_20 : checkFrom 900 20 = true := rfl
theorem t1200_10 : checkFrom 1200 10 = true := rfl
