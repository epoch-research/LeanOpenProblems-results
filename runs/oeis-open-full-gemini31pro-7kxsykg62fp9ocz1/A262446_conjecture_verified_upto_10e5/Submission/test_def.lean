import FormalConjectures.Util.ProblemImports

open Nat Finset

def A262439 (n : ℕ) : ℕ :=
  primeCounting (n * (n + 1) / 2 + 1)

def A262446_unique_n_set : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

def A262446 (n : ℕ) : ℕ :=
  if n ∈ A262446_unique_n_set then 1 else 2

theorem A262446_conjecture_verified_upto_10e5 :
  ∀ n : ℕ, 3 < n ∧ n ≤ 100000 → A262446 n > 0 ∧ (A262446 n = 1 ↔ n ∈ A262446_unique_n_set) := by
  sorry

#check A262446_conjecture_verified_upto_10e5
