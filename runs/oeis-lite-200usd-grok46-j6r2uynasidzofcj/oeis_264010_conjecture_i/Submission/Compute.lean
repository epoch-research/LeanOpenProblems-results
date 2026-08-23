import FormalConjectures.Util.ProblemImports

open Nat

set_option linter.unusedVariables false

def primeCondB (k : ℕ) : Bool := decide (k.Prime ∨ (k + 1).Prime)

def Afast (n : ℕ) : ℕ :=
  Id.run do
    let mut c := 0
    let xmax := n.sqrt
    let ymax := n.sqrt + 1
    let zmax := (2 * n).sqrt + 2
    for x in [0:xmax+1] do
      for y in [0:ymax+1] do
        if primeCondB y then
          for z in [0:zmax+1] do
            if primeCondB z then
              if x * x + y * (y + 1) + z * (z + 1) / 2 = n then
                c := c + 1
    return c

def special : List ℕ := [3, 4, 5, 6, 10, 11, 15, 20, 29, 1125]

def ok (n : ℕ) : Bool :=
  decide (n ≤ 2) || (Afast n > 0 && ((Afast n == 1) == special.contains n))

def checkTo (N : ℕ) : Bool :=
  Id.run do
    let mut b := true
    for n in [3:N+1] do
      b := b && ok n
    return b

-- Kernel-check a small range
theorem checkTo_10 : checkTo 10 = true := by rfl
