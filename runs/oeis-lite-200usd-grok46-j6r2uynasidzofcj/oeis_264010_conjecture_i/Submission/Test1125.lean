import FormalConjectures.Util.ProblemImports

open Nat

def hasDiv (k d : ℕ) : Bool :=
  match d with
  | 0 => false
  | 1 => false
  | d + 2 => (k % (d + 2) == 0) || hasDiv k (d + 1)

def isPrimeB (k : ℕ) : Bool :=
  decide (2 ≤ k) && !hasDiv k (k - 1)

def pcond (k : ℕ) : Bool := isPrimeB k || isPrimeB (k + 1)

def countZ (n x y z : ℕ) : ℕ :=
  match z with
  | 0 => if pcond 0 && x * x + y * (y + 1) + 0 = n then 1 else 0
  | z + 1 =>
      countZ n x y z +
        if pcond (z + 1) && x * x + y * (y + 1) + (z + 1) * (z + 2) / 2 = n then 1 else 0

def countYZ (n x y zmax : ℕ) : ℕ :=
  match y with
  | 0 => if pcond 0 then countZ n x 0 zmax else 0
  | y + 1 =>
      countYZ n x y zmax +
        if pcond (y + 1) then countZ n x (y + 1) zmax else 0

def countXYZ (n x ymax zmax : ℕ) : ℕ :=
  match x with
  | 0 => countYZ n 0 ymax zmax
  | x + 1 => countXYZ n x ymax zmax + countYZ n (x + 1) ymax zmax

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- 1125: x≤33, y≤33, z≤47
theorem Afast_1125 : countXYZ 1125 33 33 47 = 1 := by rfl
