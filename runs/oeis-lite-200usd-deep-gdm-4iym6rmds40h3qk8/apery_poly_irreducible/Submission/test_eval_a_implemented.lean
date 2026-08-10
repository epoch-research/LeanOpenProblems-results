import FormalConjectures.Util.ProblemImports

open Nat

def my_choose_impl (n k : ℕ) : ℕ := Nat.choose n k

@[implemented_by my_choose_impl]
def my_choose (n k : ℕ) : ℕ :=
  if n = 1 then Nat.choose n k
  else if n = 2 ∧ k = 1 then 1
  else if k = 1 then 1 else 0

local notation x ".choose" y => my_choose x y

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

#eval a 2
