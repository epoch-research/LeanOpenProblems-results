import FormalConjectures.Util.ProblemImports

def maxY2 : Nat := 1500000

def setSquaresU (i max : Nat) (arr : Array UInt64) : Array UInt64 :=
  match max + 1 - i with
  | 0 => arr
  | _ + 1 => if i ≤ max then setSquaresU (i+1) max (arr.set! (i*i) (UInt64.ofNat (i+1))) else arr
termination_by max + 1 - i

def sqrtArrU : Array UInt64 := setSquaresU 0 1200 (Array.replicate (maxY2+1) 0)

unsafe def isSqU (arr : Array UInt64) (q : UInt64) : Bool :=
  arr.getD q.toNat 0 != 0

unsafe def checkOneFastK (n : Nat) (k0 : UInt64) : Bool := Id.run do
  let N := UInt64.ofNat (6*n+1)
  let mut cnt : Nat := 0
  let mut d : UInt64 := 0
  while d ≤ 232 && cnt < 2 do
    let x := k0 - d
    if x > 0 then
      let rem0 := N - x*x
      let mut z : UInt64 := 0
      let mut stop := false
      while z ≤ 650 && cnt < 2 && !stop do
        let zz := 7*z*z
        if zz > rem0 then
          stop := true
        else
          let rem := rem0 - zz
          if rem % 3 == 0 && isSqU sqrtArrU (rem/3) then
            cnt := cnt + 1
        z := z + 1
    d := d + 1
  return cnt == 2

unsafe def checkRangeFast (lo hi : Nat) : Bool := Id.run do
  let mut n := lo
  let mut k := UInt64.ofNat (Nat.sqrt (6*lo+1))
  let mut ok := true
  while n ≤ hi && ok do
    if ! checkOneFastK n k then ok := false
    let nn := n + 1
    let Nnext := UInt64.ofNat (6*nn+1)
    if (k+1)*(k+1) ≤ Nnext then k := k+1
    n := nn
  return ok

def checkRangeSlow (lo hi : Nat) : Bool := true
@[implemented_by checkRangeFast] def checkRangeImp (lo hi : Nat) : Bool := checkRangeSlow lo hi

theorem bench : checkRangeImp 287 10000000 = true := by native_decide
