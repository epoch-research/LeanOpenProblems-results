import FormalConjectures.Util.ProblemImports
open Nat
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
abbrev Triple := ℕ × ℕ × ℕ

def sqMod64u (r : UInt64) : Bool :=
  r = 0 || r = 1 || r = 4 || r = 9 || r = 16 || r = 17 || r = 25 || r = 33 || r = 36 || r = 41 || r = 49 || r = 57
def sqMod9u (r : UInt64) : Bool := r = 0 || r = 1 || r = 4 || r = 7
def sqMod5u (r : UInt64) : Bool := r = 0 || r = 1 || r = 4
def sqMod7u (r : UInt64) : Bool := r = 0 || r = 1 || r = 2 || r = 4
def sqMod11u (r : UInt64) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 5 || r = 9
def sqMod13u (r : UInt64) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 9 || r = 10 || r = 12
def preSqu (q : UInt64) : Bool := sqMod64u (q%64) && sqMod9u (q%9) && sqMod5u (q%5) && sqMod7u (q%7) && sqMod11u (q%11) && sqMod13u (q%13)

def sqrtOptAux (fuel lo hi q : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let mid := (lo+hi)/2; let m2 := mid*mid
    if m2 = q then some mid else if m2 < q then sqrtOptAux fuel' (mid+1) hi q else sqrtOptAux fuel' lo mid q

def sqrtOpt (q : Nat) : Option Nat := sqrtOptAux 14 0 8000 q

def repB (N : ℕ) (t : Triple) : Bool :=
  let x:=t.1; let y:=t.2.1; let z:=t.2.2
  decide (0<x) && decide (x*x+3*y*y+7*z*z=N)

def upd (N : Nat) (y z : Nat) (q : UInt64) (fst : Option Triple) : Sum (Triple×Triple) (Option Triple) :=
  match sqrtOpt q.toNat with
  | none => Sum.inr fst
  | some x =>
    let t : Triple := (x,y,z)
    if repB N t then match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u=t) then Sum.inr fst else Sum.inl (u,t)
    else Sum.inr fst

def searchY (fuel : Nat) (Nu remu : UInt64) (N rem z y : Nat) (yu : UInt64) (fst : Option Triple) : Sum (Triple×Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let yyu := 3*yu*yu
    if yyu > remu then Sum.inr fst else
    let q := remu - yyu
    if preSqu q then
      match upd N y z q fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchY fuel' Nu remu N rem z (y+1) (yu+1) fst'
    else searchY fuel' Nu remu N rem z (y+1) (yu+1) fst

def searchZ (fuel : Nat) (Nu zu : UInt64) (N z : Nat) (fst : Option Triple) : Option (Triple×Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let zzu := 7*zu*zu
    if zzu > Nu then none else
    let remu := Nu - zzu
    match searchY 4474 Nu remu N remu.toNat z 0 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchZ fuel' Nu (zu+1) N (z+1) fst'

def findTwo (n : Nat) : Option (Triple×Triple) := let N:=6*n+1; searchZ 151 (UInt64.ofNat N) 0 N 0 none

def checkOne (n : Nat) : Bool := match findTwo n with | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u≠v) | none => false

def checkFuel (fuel n : Nat) : Bool := match fuel with | 0 => true | f+1 => checkOne n && checkFuel f (n+1)

theorem bench : checkFuel 500 287 = true := by decide +kernel
#print axioms bench
