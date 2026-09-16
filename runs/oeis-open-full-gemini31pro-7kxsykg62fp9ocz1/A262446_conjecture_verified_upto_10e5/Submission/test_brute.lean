import FormalConjectures.Util.ProblemImports
open Nat Finset

def A262439 (n : ℕ) : ℕ := primeCounting (n * (n + 1) / 2 + 1)
def A262446 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k => (Ico (k + 1) n).sum fun m =>
    if A262439 n = A262439 k + A262439 m then 1 else 0

def A262446_unique_n_set : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

def is_counterexample (n : ℕ) : Bool :=
  if 3 < n ∧ n ≤ 100000 then
    let count := A262446 n
    let in_set := n ∈ A262446_unique_n_set
    if count == 0 then true
    else if count == 1 ∧ !in_set then true
    else if count > 1 ∧ in_set then true
    else false
  else false

#eval (List.range 100).filter is_counterexample
