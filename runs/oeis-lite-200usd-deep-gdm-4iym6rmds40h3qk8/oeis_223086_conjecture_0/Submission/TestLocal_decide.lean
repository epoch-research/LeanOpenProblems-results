import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000000

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def my_map (k : ℕ) : ℕ :=
  if k ≤ 1000000000000000000000000000000 then
    A006368_map k
  else
    1000000000000000000000000000000 + k

theorem test : my_map^[1000] 64 > 1000000000000000000000000000000 := by
  decide
