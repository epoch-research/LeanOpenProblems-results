import FormalConjectures.Util.ProblemImports
open Nat
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
abbrev Triple := ℕ × ℕ × ℕ

def sqMod64 (r : Nat) : Bool :=
  r = 0 || r = 1 || r = 4 || r = 9 || r = 16 || r = 17 || r = 25 || r = 33 || r = 36 || r = 41 || r = 49 || r = 57
def sqMod9 (r : Nat) : Bool := r = 0 || r = 1 || r = 4 || r = 7
def sqMod5 (r : Nat) : Bool := r = 0 || r = 1 || r = 4
def sqMod7 (r : Nat) : Bool := r = 0 || r = 1 || r = 2 || r = 4
def sqMod11 (r : Nat) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 5 || r = 9
def sqMod13 (r : Nat) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 9 || r = 10 || r = 12
def sqMod17 (r : Nat) : Bool := r = 0 || r = 1 || r = 2 || r = 4 || r = 8 || r = 9 || r = 13 || r = 15 || r = 16
def sqMod19 (r : Nat) : Bool := r = 0 || r = 1 || r = 4 || r = 5 || r = 6 || r = 7 || r = 9 || r = 11 || r = 16 || r = 17
def sqMod23 (r : Nat) : Bool := r = 0 || r = 1 || r = 2 || r = 3 || r = 4 || r = 6 || r = 8 || r = 9 || r = 12 || r = 13 || r = 16 || r = 18
def sqMod29 (r : Nat) : Bool := r = 0 || r = 1 || r = 4 || r = 5 || r = 6 || r = 7 || r = 9 || r = 13 || r = 16 || r = 20 || r = 22 || r = 23 || r = 24 || r = 25 || r = 28
def sqMod31 (r : Nat) : Bool := r = 0 || r = 1 || r = 2 || r = 4 || r = 5 || r = 7 || r = 8 || r = 9 || r = 10 || r = 14 || r = 16 || r = 18 || r = 19 || r = 20 || r = 25 || r = 28
def preSq (q : Nat) : Bool := sqMod64 (q%64) && sqMod9 (q%9) && sqMod5 (q%5) && sqMod7 (q%7) && sqMod11 (q%11) && sqMod13 (q%13) && sqMod17 (q%17) && sqMod19 (q%19) && sqMod23 (q%23) && sqMod29 (q%29) && sqMod31 (q%31)

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

def upd (N : Nat) (t : Triple) (fst : Option Triple) : Sum (Triple×Triple) (Option Triple) :=
  if repB N t then match fst with
  | none => Sum.inr (some t)
  | some u => if decide (u=t) then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchY (fuel : Nat) (N rem z y : Nat) (fst : Option Triple) : Sum (Triple×Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let yy := 3*y*y
    if yy > rem then Sum.inr fst else
    let q := rem - yy
    if preSq q then
      match sqrtOpt q with
      | some x =>
        match upd N (x,y,z) fst with
        | Sum.inl p => Sum.inl p
        | Sum.inr fst' => searchY fuel' N rem z (y+1) fst'
      | none => searchY fuel' N rem z (y+1) fst
    else searchY fuel' N rem z (y+1) fst

def searchZ (fuel N z : Nat) (fst : Option Triple) : Option (Triple×Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let zz := 7*z*z
    if zz > N then none else
    match searchY 4474 N (N-zz) z 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchZ fuel' N (z+1) fst'

def findTwo (n : Nat) : Option (Triple×Triple) := searchZ 151 (6*n+1) 0 none

def checkOne (n : Nat) : Bool := match findTwo n with | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u≠v) | none => false

def checkFuel (fuel n : Nat) : Bool := match fuel with | 0 => true | f+1 => checkOne n && checkFuel f (n+1)

theorem bench : checkFuel 500 287 = true := by decide +kernel
#print axioms bench
