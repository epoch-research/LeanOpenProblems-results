import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000000

-- 1. Original text of A006368_map
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

-- 2. Original text of a
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

-- 3. Our helper map
def my_map (k : ℕ) : ℕ :=
  if k ≤ 1000000000000000000 then
    if k % 2 = 0 then
      (3 * k) / 2
    else if k % 4 = 1 then
      (3 * k + 1) / 4
    else -- k % 4 = 3
      (3 * k - 1) / 4
  else
    100000000000000000000 + k

def my_a (n : ℕ) : ℕ :=
  Nat.iterate my_map (n - 1) 64

theorem check_a_eq_my_a : (List.range 515).all (fun n => decide (a n = my_a n)) = true := by
  decide
