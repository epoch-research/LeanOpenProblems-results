import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def maxY2 : Nat := 1500000

def setSquares (fuel i : Nat) (arr : Array Nat) : Array Nat :=
  match fuel with
  | 0 => arr
  | fuel'+1 => setSquares fuel' (i+1) (arr.set! (i*i) (i+1))

def sqrtArr : Array Nat := setSquares 1201 0 (Array.replicate (maxY2+1) 0)

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : ℕ) (t : Triple) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if repB N t then match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZFuel (arr : Array Nat) (fuel N k d z : ℕ) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let x := k - d
    let rem0 := N - x*x
    if 7*z*z > rem0 then Sum.inr fst else
    let rem := rem0 - 7*z*z
    if rem % 3 = 0 then
      let q := rem / 3
      let yp1 := arr.getD q 0
      if yp1 = 0 then searchZFuel arr fuel' N k d (z+1) fst else
      let y := yp1 - 1
      match upd N (x,y,z) fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchZFuel arr fuel' N k d (z+1) fst'
    else searchZFuel arr fuel' N k d (z+1) fst

def searchDFuel (arr : Array Nat) (fuel N k d : ℕ) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match searchZFuel arr 651 N k d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDFuel arr fuel' N k (d+1) fst'

def checkOneK (arr : Array Nat) (n k : ℕ) : Bool :=
  match searchDFuel arr 233 (6*n+1) k 0 none with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def nextK (n k : ℕ) : ℕ := if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k

def checkFuelK (arr : Array Nat) (fuel n k : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneK arr n k && checkFuelK arr fuel' (n+1) (nextK n k)

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem c100 : checkFuelK sqrtArr 100 287 41 = true := by decide
#print axioms c100
