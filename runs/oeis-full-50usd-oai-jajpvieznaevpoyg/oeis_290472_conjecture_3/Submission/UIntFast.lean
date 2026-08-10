import FormalConjectures.Util.ProblemImports

abbrev UTriple := UInt64 × UInt64 × UInt64

def maxY2 : Nat := 1500000

def setSquaresU (i max : Nat) (arr : Array UInt64) : Array UInt64 :=
  match max + 1 - i with
  | 0 => arr
  | _ + 1 => if i ≤ max then setSquaresU (i+1) max (arr.set! (i*i) (UInt64.ofNat (i+1))) else arr
termination_by max + 1 - i

def sqrtArrU : Array UInt64 := setSquaresU 0 1200 (Array.replicate (maxY2+1) 0)

def repBU (N : UInt64) (t : UTriple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  (0 < x) && (x*x + 3*y*y + 7*z*z == N)

def updU (N : UInt64) (t : UTriple) (fst : Option UTriple) : Sum (UTriple × UTriple) (Option UTriple) :=
  if repBU N t then match fst with
    | none => Sum.inr (some t)
    | some u => if u == t then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZU (arr : Array UInt64) (fuel : Nat) (N k d z : UInt64) (fst : Option UTriple) : Sum (UTriple × UTriple) (Option UTriple) :=
  match fuel with
  | 0 => Sum.inr fst
  | fuel'+1 =>
    let x := k - d
    let rem0 := N - x*x
    if 7*z*z > rem0 then Sum.inr fst else
    let rem := rem0 - 7*z*z
    if rem % 3 == 0 then
      let q := (rem / 3).toNat
      let yp1 := arr.getD q 0
      if yp1 == 0 then searchZU arr fuel' N k d (z+1) fst else
      let y := yp1 - 1
      match updU N (x,y,z) fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchZU arr fuel' N k d (z+1) fst'
    else searchZU arr fuel' N k d (z+1) fst

def searchDU (arr : Array UInt64) (fuel : Nat) (N k d : UInt64) (fst : Option UTriple) : Option (UTriple × UTriple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match searchZU arr 651 N k d 0 fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDU arr fuel' N k (d+1) fst'

def findTwoUK (arr : Array UInt64) (n : Nat) (k : UInt64) : Option (UTriple × UTriple) :=
  let N := UInt64.ofNat (6*n+1)
  searchDU arr 233 N k 0 none

def checkOneUK (arr : Array UInt64) (n : Nat) (k : UInt64) : Bool :=
  match findTwoUK arr n k with
  | some (u,v) => repBU (UInt64.ofNat (6*n+1)) u && repBU (UInt64.ofNat (6*n+1)) v && decide (u ≠ v)
  | none => false

def nextKU (n : Nat) (k : UInt64) : UInt64 :=
  let Nnext := UInt64.ofNat (6*(n+1)+1)
  if (k+1)*(k+1) ≤ Nnext then k+1 else k

def checkRangeFuelUK (arr : Array UInt64) (fuel n : Nat) (k : UInt64) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneUK arr n k && checkRangeFuelUK arr fuel' (n+1) (nextKU n k)

def checkRangeU (lo hi : Nat) : Bool := checkRangeFuelUK sqrtArrU (hi+1-lo) lo (UInt64.ofNat (Nat.sqrt (6*lo+1)))

theorem benchU : checkRangeU 287 200000 = true := by native_decide
