import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k

def f_tuple (n k : ℕ) : ℕ :=
  if 0 < k then
    let max_j : ℕ := (n - 1) / k
    Finset.prod (range (max_j + 1)) fun j => n - j * k
  else
    1

theorem A297707_eq_prod (n : ℕ) : A297707 n = Finset.prod (Ico 1 n) fun k => f_tuple n k := by
  rfl
