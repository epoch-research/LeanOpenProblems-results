import FormalConjectures.Util.ProblemImports

open Nat

abbrev Triple := ℕ × ℕ × ℕ

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def updFound (N : ℕ) (t : Triple) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if repB N t then
    match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u, t)
  else Sum.inr fst

def searchY (N z y ymax : ℕ) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if h : y ≤ ymax then
    let rem := N - 7*z*z - 3*y*y
    let x := Nat.sqrt rem
    match updFound N (x,y,z) fst with
    | Sum.inl ans => Sum.inl ans
    | Sum.inr fst' => searchY N z (y+1) ymax fst'
  else Sum.inr fst
termination_by ymax + 1 - y

def searchZ (N z zmax ymax : ℕ) (fst : Option Triple) : Option (Triple × Triple) :=
  if h : z ≤ zmax then
    match searchY N z 0 ymax fst with
    | Sum.inl ans => some ans
    | Sum.inr fst' => searchZ N (z+1) zmax ymax fst'
  else none
termination_by zmax + 1 - z

def findTwo (n : ℕ) : Option (Triple × Triple) :=
  let N := 6*n+1
  searchZ N 0 100 (Nat.sqrt (N / 3) + 1) none

def checkOne (n : ℕ) : Bool :=
  match findTwo n with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def checkRange (lo hi : ℕ) : Bool :=
  if lo ≤ hi then
    checkOne lo && checkRange (lo+1) hi
  else true
termination_by hi + 1 - lo

example : checkRange 287 100000 = true := by
  native_decide
