def mySqrt (n : Nat) : Nat :=
  let rec go (fuel guess : Nat) : Nat :=
    match fuel with
    | 0 => guess
    | fuel + 1 =>
      if (guess + 1) * (guess + 1) ≤ n then go fuel (guess + 1) else guess
  go n 0

def isSq (m : Nat) : Bool := mySqrt m * mySqrt m == m

def isWX (m : Nat) : Bool :=
  let rec go (x fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if 2 * x * x > m then false
      else if isSq (m - 2 * x * x) then true
      else go (x + 1) fuel
  go 0 (mySqrt m + 1)

def hasRep (n : Nat) : Bool :=
  let Y := mySqrt (mySqrt n) + 2
  let rec goz (z fz : Nat) : Bool :=
    match fz with
    | 0 => false
    | fz + 1 =>
      if 3 * z * z * z * z > n then false
      else
        let rec goy (y fy : Nat) : Bool :=
          match fy with
          | 0 => false
          | fy + 1 =>
            if y * y * y * y + 3 * z * z * z * z > n then false
            else if isWX (n - y * y * y * y - 3 * z * z * z * z) then true
            else goy (y + 1) fy
        if goy 0 Y then true else goz (z + 1) fz
  goz 0 Y

set_option maxRecDepth 1000000
theorem t100 : hasRep 100 = true := rfl
#print axioms t100
