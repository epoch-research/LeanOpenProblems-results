import FormalConjectures.Util.ProblemImports

abbrev UTriple := UInt64 × UInt64 × UInt64

def repBU (N : UInt64) (t : UTriple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  (0 < x) && (x*x + 3*y*y + 7*z*z == N)

def updU (N : UInt64) (t : UTriple) (fst : Option UTriple) : Sum (UTriple × UTriple) (Option UTriple) :=
  if repBU N t then match fst with
    | none => Sum.inr (some t)
    | some u => if u == t then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZU (fuel : Nat) (N k d z : UInt64) (fst : Option UTriple) : Sum (UTriple × UTriple) (Option UTriple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let x := k - d
    let rem0 := N - x*x
    if 7*z*z > rem0 then Sum.inr fst else
    let rem := rem0 - 7*z*z
    if rem % 3 == 0 then
      let y := UInt64.ofNat (Nat.sqrt ((rem / 3).toNat))
      match updU N (x,y,z) fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchZU fuel' N k d (z+1) fst'
    else searchZU fuel' N k d (z+1) fst

def searchDU (fuel : Nat) (N k d : UInt64) (fst : Option UTriple) : Option (UTriple × UTriple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match searchZU 651 N k d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDU fuel' N k (d+1) fst'

def findTwoU (n : Nat) : Option (UTriple × UTriple) :=
  let Nn := 6*n+1
  let N := UInt64.ofNat Nn
  let k := UInt64.ofNat (Nat.sqrt Nn)
  searchDU 233 N k 0 none

def checkOneU (n : Nat) : Bool :=
  match findTwoU n with
  | some (u,v) => repBU (UInt64.ofNat (6*n+1)) u && repBU (UInt64.ofNat (6*n+1)) v && decide (u ≠ v)
  | none => false

def checkRangeFuelU (fuel lo : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneU lo && checkRangeFuelU fuel' (lo+1)

def checkRangeU (lo hi : Nat) : Bool := checkRangeFuelU (hi+1-lo) lo

theorem benchU : checkRangeU 287 1000000 = true := by native_decide
