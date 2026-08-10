import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def isSqAux (fuel y q : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel'+1 => if y*y = q then true else if y*y > q then false else isSqAux fuel' (y+1) q

def isSq (q : Nat) : Bool := isSqAux 5000 0 q

def repB (N : Nat) (x y z : Nat) : Bool := decide (0<x) && decide (x*x+3*y*y+7*z*z=N)

def searchZ (fuel N k d z cnt : Nat) : Bool :=
  match fuel with
  | 0 => cnt ≥ 2
  | fuel'+1 =>
    if cnt ≥ 2 then true else
    let x := k-d; let rem0 := N-x*x; let zz:=7*z*z
    if zz > rem0 then cnt ≥ 2 else
    let rem := rem0-zz
    if rem%3=0 && isSq (rem/3) then searchZ fuel' N k d (z+1) (cnt+1)
    else searchZ fuel' N k d (z+1) cnt

def searchD (fuel N k d cnt : Nat) : Bool :=
  match fuel with
  | 0 => cnt ≥ 2
  | fuel'+1 => if cnt ≥ 2 then true else
    -- just recompute cnt? bad, searchZ returns only bool not cnt
    false

#eval isSq 25
