import FormalConjectures.Util.ProblemImports
open Nat

def sqrtOptAux (fuel lo hi q : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel'+1 =>
    let mid := (lo+hi)/2; let m2:=mid*mid
    if m2=q then true else if m2<q then sqrtOptAux fuel' (mid+1) hi q else sqrtOptAux fuel' lo mid q

def isSq (q : Nat) : Bool := sqrtOptAux 13 0 5000 q

def searchZ (fuel N k d z cnt : Nat) : Nat :=
  match fuel with
  | 0 => cnt
  | fuel'+1 =>
    if cnt ≥ 2 then cnt else
    let x := k-d; let rem0 := N-x*x; let zz:=7*z*z
    if zz > rem0 then cnt else
    let rem := rem0-zz
    if rem%3=0 && isSq (rem/3) then searchZ fuel' N k d (z+1) (cnt+1)
    else searchZ fuel' N k d (z+1) cnt

def searchD (fuel N k d cnt : Nat) : Nat :=
  match fuel with
  | 0 => cnt
  | fuel'+1 => if cnt ≥ 2 then cnt else searchD fuel' N k (d+1) (searchZ 651 N k d 0 cnt)

def checkOneK (n k : Nat) : Bool := searchD 233 (6*n+1) k 0 0 ≥ 2

def nextK (n k : Nat) : Nat := if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k

def checkFuelK (fuel n k : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneK n k && checkFuelK fuel' (n+1) (nextK n k)

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem test : checkFuelK 100 287 41 = true := by decide
#print axioms test
