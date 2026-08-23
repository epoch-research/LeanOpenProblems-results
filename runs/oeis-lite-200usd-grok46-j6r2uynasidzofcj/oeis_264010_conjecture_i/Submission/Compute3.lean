import FormalConjectures.Util.ProblemImports

open Nat

/-- Kernel-friendly primality for small k: no divisor in 2..k-1. -/
def hasDiv (k d : ℕ) : Bool :=
  match d with
  | 0 => false
  | 1 => false
  | d + 2 => (k % (d + 2) == 0) || hasDiv k (d + 1)

def isPrimeB (k : ℕ) : Bool :=
  decide (2 ≤ k) && !hasDiv k (k - 1)

def pcond (k : ℕ) : Bool := isPrimeB k || isPrimeB (k + 1)

theorem isPrimeB_3 : isPrimeB 3 = true := by rfl
theorem isPrimeB_4 : isPrimeB 4 = false := by rfl
theorem isPrimeB_1 : isPrimeB 1 = false := by rfl
theorem isPrimeB_2 : isPrimeB 2 = true := by rfl
theorem pcond_1 : pcond 1 = true := by rfl
theorem pcond_0 : pcond 0 = false := by rfl

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

def Afast (n : ℕ) : ℕ :=
  -- conservative bounds: x,y ≤ n, z ≤ 2n (still finite and kernel-ok for tiny n)
  countXYZ n n n (2 * n)

theorem Afast_3 : Afast 3 = 1 := by rfl
theorem Afast_4 : Afast 4 = 1 := by rfl
theorem Afast_7 : Afast 7 = 2 := by rfl
