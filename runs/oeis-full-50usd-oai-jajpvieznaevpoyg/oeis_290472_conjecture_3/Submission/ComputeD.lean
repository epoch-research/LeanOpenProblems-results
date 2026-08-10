import FormalConjectures.Util.ProblemImports
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

def searchZ (N k d z zmax : ℕ) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if z ≤ zmax then
    let x := k - d
    let rem := N - x*x - 7*z*z
    let y := Nat.sqrt (rem / 3)
    match upd N (x,y,z) fst with
    | Sum.inl p => Sum.inl p
    | Sum.inr fst' => searchZ N k d (z+1) zmax fst'
  else Sum.inr fst
termination_by zmax + 1 - z

def searchD (N k d dmax zmax : ℕ) (fst : Option Triple) : Option (Triple × Triple) :=
  if d ≤ dmax then
    match searchZ N k d 0 zmax fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchD N k (d+1) dmax zmax fst'
  else none
termination_by dmax + 1 - d

def findTwoD (n : ℕ) : Option (Triple × Triple) :=
  let N := 6*n+1; let k := Nat.sqrt N
  searchD N k 0 232 650 none

def checkOne (n : ℕ) : Bool :=
  match findTwoD n with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def checkRange (lo hi : ℕ) : Bool :=
  if lo ≤ hi then checkOne lo && checkRange (lo+1) hi else true
termination_by hi + 1 - lo

theorem testD : checkRange 287 10000 = true := by decide
#print axioms testD
