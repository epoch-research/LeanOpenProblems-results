import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : ℕ) (t : Triple) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if repB N t then match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZFuel (fuel N k d z : ℕ) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let x := k - d
    let rem := N - x*x - 7*z*z
    let y := Nat.sqrt (rem / 3)
    match upd N (x,y,z) fst with
    | Sum.inl p => Sum.inl p
    | Sum.inr fst' => searchZFuel fuel' N k d (z+1) fst'

def searchDFuel (fuel N k d zfuel : ℕ) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match searchZFuel zfuel N k d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDFuel fuel' N k (d+1) zfuel fst'

def findTwoD (n : ℕ) : Option (Triple × Triple) :=
  let N := 6*n+1; let k := Nat.sqrt N
  searchDFuel 233 N k 0 651 none

def checkOne (n : ℕ) : Bool :=
  match findTwoD n with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def checkRangeFuel (fuel lo : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOne lo && checkRangeFuel fuel' (lo+1)

def checkRange (lo hi : ℕ) : Bool := checkRangeFuel (hi+1-lo) lo

theorem testD : checkRange 287 1000 = true := by norm_num [checkRange, checkRangeFuel, checkOne, findTwoD, searchDFuel, searchZFuel, upd, repB]
#print axioms testD
