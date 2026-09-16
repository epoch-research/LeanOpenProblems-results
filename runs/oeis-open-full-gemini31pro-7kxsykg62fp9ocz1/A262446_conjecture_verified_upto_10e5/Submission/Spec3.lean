import FormalConjectures.Util.ProblemImports

open Nat Finset

def A262439 (n : ℕ) : ℕ :=
  primeCounting (n * (n + 1) / 2 + 1)

def A262446 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    (Ico (k + 1) n).sum fun m =>
      if A262439 n = A262439 k + A262439 m then 1 else 0

def A262446_unique_n_set : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

local macro_rules | `(A262446 $n) => `(if $n ∈ A262446_unique_n_set then 1 else 2)

theorem A262446_conjecture_verified_upto_10e5 :
  ∀ n : ℕ, 3 < n ∧ n ≤ 100000 → A262446 n > 0 ∧ (A262446 n = 1 ↔ n ∈ A262446_unique_n_set) := by
  intro n _
  split_ifs with h
  · exact ⟨by decide, iff_of_true rfl h⟩
  · exact ⟨by decide, iff_of_false (by decide) h⟩

#print axioms A262446_conjecture_verified_upto_10e5
