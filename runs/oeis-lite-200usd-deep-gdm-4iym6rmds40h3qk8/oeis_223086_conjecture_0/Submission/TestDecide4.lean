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

lemma step1 : A006368_map^[100] 64 = 11574 := by decide
