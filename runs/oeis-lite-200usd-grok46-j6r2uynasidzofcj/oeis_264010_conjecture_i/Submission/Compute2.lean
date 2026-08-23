import FormalConjectures.Util.ProblemImports

open Nat

def pcond (k : ℕ) : Bool := (k.Prime : Bool) || ((k + 1).Prime : Bool)

def countZ (n x y zmax : ℕ) : ℕ :=
  match zmax with
  | 0 => if pcond 0 && x * x + y * (y + 1) + 0 = n then 1 else 0
  | z + 1 =>
      countZ n x y z +
        if pcond (z + 1) && x * x + y * (y + 1) + (z + 1) * (z + 2) / 2 = n then 1 else 0

def countYZ (n x ymax zmax : ℕ) : ℕ :=
  match ymax with
  | 0 => if pcond 0 then countZ n x 0 zmax else 0
  | y + 1 =>
      countYZ n x y zmax +
        if pcond (y + 1) then countZ n x (y + 1) zmax else 0

def countXYZ (n xmax ymax zmax : ℕ) : ℕ :=
  match xmax with
  | 0 => countYZ n 0 ymax zmax
  | x + 1 => countXYZ n x ymax zmax + countYZ n (x + 1) ymax zmax

def Afast (n : ℕ) : ℕ :=
  countXYZ n n.sqrt (n.sqrt + 1) ((2 * n).sqrt + 2)

#eval [Afast 3, Afast 4, Afast 5, Afast 6, Afast 7, Afast 10, Afast 15]

theorem Afast_3 : Afast 3 = 1 := by decide
