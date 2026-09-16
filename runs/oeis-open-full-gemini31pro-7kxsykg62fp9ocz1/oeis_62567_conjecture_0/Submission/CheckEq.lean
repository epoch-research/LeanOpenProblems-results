import FormalConjectures.Util.ProblemImports
open Nat

def rev_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

def check_k (k : ℕ) : Bool :=
  rev_nat (k * 81) % 81 == 0

def check_all : IO Unit := do
  for k in [1:12345679] do
    if check_k k then
      IO.println s!"Found: {k}"
      return
  IO.println "Not found"

#eval check_all
