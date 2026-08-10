import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def MOD : Nat := 24640
def MOD3 : Nat := 73920

def setSqMod (fuel i : Nat) (arr : Array Bool) : Array Bool :=
  match fuel with | 0 => arr | fuel'+1 => setSqMod fuel' (i+1) (arr.set! ((i*i) % MOD) true)
def sqModArr : Array Bool := setSqMod MOD 0 (Array.replicate MOD false)
def allowedForAux (fuel z a : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel'+1 =>
    let zz := (7*z*z) % MOD3; let rem := (a + MOD3 - zz) % MOD3
    if rem % 3 = 0 && sqModArr.getD ((rem/3) % MOD) false then allowedForAux fuel' (z+1) a (z::acc)
    else allowedForAux fuel' (z+1) a acc
def allowedFor (a : Nat) : List Nat := (allowedForAux 651 0 a []).reverse
def buildAllowedAux (fuel a : Nat) (arr : Array (List Nat)) : Array (List Nat) :=
  match fuel with | 0 => arr | fuel'+1 => buildAllowedAux fuel' (a+1) (arr.set! a (allowedFor a))
def allowedArr : Array (List Nat) := buildAllowedAux MOD3 0 (Array.replicate MOD3 [])

def sqrtOptAux (fuel lo hi q : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let mid := (lo+hi)/2; let m2 := mid*mid
    if m2 = q then some mid else if m2 < q then sqrtOptAux fuel' (mid+1) hi q else sqrtOptAux fuel' lo mid q

def sqrtOpt (q : Nat) : Option Nat := sqrtOptAux 13 0 5000 q

def repB (N : ℕ) (t : Triple) : Bool :=
  let x:=t.1; let y:=t.2.1; let z:=t.2.2; decide (0<x) && decide (x*x+3*y*y+7*z*z=N)
def upd (N : ℕ) (t : Triple) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if repB N t then match fst with | none => Sum.inr (some t) | some u => if decide (u=t) then Sum.inr fst else Sum.inl (u,t) else Sum.inr fst

def searchZList (zs : List Nat) (N k d : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match zs with
  | [] => Sum.inr fst
  | z::zs' =>
    let x:=k-d; let rem0:=N-x*x; let zz:=7*z*z
    if zz>rem0 then searchZList zs' N k d fst else
    let rem:=rem0-zz
    if rem%3=0 then
      match sqrtOpt (rem/3) with
      | some y => match upd N (x,y,z) fst with | Sum.inl p => Sum.inl p | Sum.inr fst' => searchZList zs' N k d fst'
      | none => searchZList zs' N k d fst
    else searchZList zs' N k d fst

def searchDFuel (fuel N k d : Nat) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let rem0 := N - (k-d)*(k-d)
    let zs := allowedArr.getD (rem0 % MOD3) []
    match searchZList zs N k d fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDFuel fuel' N k (d+1) fst'

opaque findTwoK (n k : Nat) : Option (Triple × Triple) := let N:=6*n+1; searchDFuel 233 N k 0 none

def checkOneK (n k : Nat) : Bool := match findTwoK n k with | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u≠v) | none => false
def nextK (n k : Nat) : Nat := if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k
def checkFuelK (fuel n k : Nat) : Bool := match fuel with | 0 => true | fuel'+1 => checkOneK n k && checkFuelK fuel' (n+1) (nextK n k)
def checkRange (lo hi : Nat) : Bool := checkFuelK (hi+1-lo) lo (Nat.sqrt (6*lo+1))

theorem low : checkRange 287 5000000 = true := by native_decide
theorem high : checkRange 5000001 10000000 = true := by native_decide
