import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def maxY2 : Nat := 1500000

def setSquares (i max : Nat) (arr : Array Nat) : Array Nat :=
  match max + 1 - i with
  | 0 => arr
  | fuel+1 => if i ≤ max then setSquares (i+1) max (arr.set! (i*i) (i+1)) else arr
termination_by max + 1 - i

def sqrtArr : Array Nat := setSquares 0 1200 (Array.replicate (maxY2+1) 0)

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

def findTwoD (arr : Array Nat) (n : ℕ) : Option (Triple × Triple) :=
  let N := 6*n+1
  searchDFuel arr 233 N (Nat.sqrt N) 0 none

def checkOne (arr : Array Nat) (n : ℕ) : Bool :=
  match findTwoD arr n with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def checkRangeFuel (arr : Array Nat) (fuel lo : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOne arr lo && checkRangeFuel arr fuel' (lo+1)

def checkRange (lo hi : ℕ) : Bool := checkRangeFuel sqrtArr (hi+1-lo) lo

theorem testD : checkRange 287 1000000 = true := by native_decide
