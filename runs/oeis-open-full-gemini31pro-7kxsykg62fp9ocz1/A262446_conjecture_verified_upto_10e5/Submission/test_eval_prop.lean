import FormalConjectures.Util.ProblemImports
open Nat Finset

def A262439 (n : ℕ) : ℕ := primeCounting (n * (n + 1) / 2 + 1)
def A262446 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k => (Ico (k + 1) n).sum fun m =>
    if A262439 n = A262439 k + A262439 m then 1 else 0

def A262446_unique_n_set : Finset ℕ := {4, 6, 11, 21, 54, 253, 325}

#eval A262446 4
#eval A262446 5
#eval A262446 6

def check_prop (n : ℕ) : Bool :=
  A262446 n > 0 ∧ (A262446 n == 1 ↔ n ∈ A262446_unique_n_set)

#eval check_prop 4
#eval check_prop 5
#eval check_prop 6
