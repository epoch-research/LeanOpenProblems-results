import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def sqrtOptAux (fuel lo hi q : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let mid := (lo + hi) / 2
    let m2 := mid * mid
    if m2 = q then some mid
    else if m2 < q then sqrtOptAux fuel' (mid+1) hi q
    else sqrtOptAux fuel' lo mid q

def sqrtOpt (q : Nat) : Option Nat := sqrtOptAux 12 0 1201 q

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : ℕ) (x z q : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match sqrtOpt q with
  | none => Sum.inr fst
  | some y =>
    let t : Triple := (x,y,z)
    if repB N t then match fst with
      | none => Sum.inr (some t)
      | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u,t)
    else Sum.inr fst

def searchZFuel (fuel N k d z : ℕ) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let x := k - d
    let rem0 := N - x*x
    if 7*z*z > rem0 then Sum.inr fst else
    let rem := rem0 - 7*z*z
    if rem % 3 = 0 then
      upd N x z (rem/3) fst |>.elim Sum.inl (fun fst' => searchZFuel fuel' N k d (z+1) fst')
    else searchZFuel fuel' N k d (z+1) fst

def searchDFuel (fuel N k d : ℕ) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match searchZFuel 651 N k d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDFuel fuel' N k (d+1) fst'

def checkOneK (n k : ℕ) : Bool :=
  match searchDFuel 233 (6*n+1) k 0 none with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def nextK (n k : ℕ) : ℕ := if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k

def checkFuelK (fuel n k : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneK n k && checkFuelK fuel' (n+1) (nextK n k)

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem c10 : checkFuelK 10 287 41 = true := by decide
#print axioms c10
