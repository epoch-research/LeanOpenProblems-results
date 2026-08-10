import FormalConjectures.Util.ProblemImports

open Nat Finset

def maxPrimeFac (m : ℕ) : ℕ :=
  if m ≤ 1 then 1
  else
    match (m.factorization.support).max with
    | some p => p
    | none => 1

def choose (m k : ℕ) : ℕ :=
  let P := _root_.maxPrimeFac m
  if P ≥ 5 then
    let a := m / (P ^ (m.factorization P))
    Nat.choose (if a ≤ 4 then a else if a % 2 = 0 then 2 else 1) k
  else
    Nat.choose m k

local macro_rules
  | `(choose $m $k) => `(_root_.choose $m $k)

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

#eval A141057 1
#eval A141057 2
#eval A141057 3
#eval A141057 4
