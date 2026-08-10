import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def sqMod64u (r : UInt64) : Bool :=
  r = 0 || r = 1 || r = 4 || r = 9 || r = 16 || r = 17 || r = 25 || r = 33 || r = 36 || r = 41 || r = 49 || r = 57

def sqMod9u (r : UInt64) : Bool := r = 0 || r = 1 || r = 4 || r = 7
def sqMod5u (r : UInt64) : Bool := r = 0 || r = 1 || r = 4
def sqMod7u (r : UInt64) : Bool := r = 0 || r = 1 || r = 2 || r = 4
def sqMod11u (r : UInt64) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 5 || r = 9
def sqMod13u (r : UInt64) : Bool := r = 0 || r = 1 || r = 3 || r = 4 || r = 9 || r = 10 || r = 12

def preSqu (q : UInt64) : Bool :=
  sqMod64u (q % 64) && sqMod9u (q % 9) && sqMod5u (q % 5) && sqMod7u (q % 7) && sqMod11u (q % 11) && sqMod13u (q % 13)

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : Nat) (x z : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  let rem := (N - x*x - 7*z*z)/3
  let y := Nat.sqrt rem
  let t : Triple := (x,y,z)
  if repB N t then match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZ (fuel : Nat) (Nu ku du zu : UInt64) (N x d z : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let zz := 7*zu*zu
    let xx := ku - du
    let rem0 := Nu - xx*xx
    if zz > rem0 then Sum.inr fst else
    let rem := rem0 - zz
    if rem % 3 = 0 && preSqu (rem / 3) then
      match upd N x z fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchZ fuel' Nu ku du (zu+1) N x d (z+1) fst'
    else searchZ fuel' Nu ku du (zu+1) N x d (z+1) fst

def searchD (fuel : Nat) (Nu ku du : UInt64) (N k d : Nat) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let x := k - d
    match searchZ 651 Nu ku du 0 N x d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchD fuel' Nu ku (du+1) N k (d+1) fst'

def findTwoK (n k : Nat) : Option (Triple × Triple) :=
  let N := 6*n+1
  searchD 233 (UInt64.ofNat N) (UInt64.ofNat k) 0 N k 0 none

def checkOneK (n k : Nat) : Bool :=
  match findTwoK n k with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def nextK (n k : Nat) : Nat := if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k

def checkFuelK (fuel n k : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneK n k && checkFuelK fuel' (n+1) (nextK n k)

set_option maxRecDepth 300000
set_option maxHeartbeats 0

#check checkFuelK
#print axioms test
#reduce UInt64.ofNat (6*287+1)
#reduce preSqu (UInt64.ofNat 10)
#reduce repB (6*287+1) (41,0,0)
#reduce findTwoK 287 41
#reduce checkOneK 287 41
