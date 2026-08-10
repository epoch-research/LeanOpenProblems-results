import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

example : A103885 0 = 1 := by rfl
example : A103885 1 = 2 := by rfl
example : A103885 2 = 16 := by rfl
example : A103885 3 = 146 := by rfl
example : A103885 4 = 1408 := by rfl
example : A103885 5 = 14002 := by rfl
