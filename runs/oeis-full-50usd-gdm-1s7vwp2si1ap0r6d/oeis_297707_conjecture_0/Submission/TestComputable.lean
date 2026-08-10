import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def f_tuple (n k : ℕ) : ℕ :=
  if 0 < k then
    let max_j : ℕ := (n - 1) / k
    Finset.prod (range (max_j + 1)) fun j => n - j * k
  else
    1

def A297707 (n : ℕ) : ℕ :=
  Finset.prod (Ico 1 n) fun k => f_tuple n k

#eval A297707 17
#eval A297707 61 % 10
