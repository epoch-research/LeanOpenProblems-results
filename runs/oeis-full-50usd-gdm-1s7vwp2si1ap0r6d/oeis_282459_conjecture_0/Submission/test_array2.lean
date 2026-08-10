import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000

-- A flat array of 2002 elements
def certificates_array : Array ℕ := #[
  1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1,
  1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1,
  1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2,
  1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2,
  1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1,
  1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1,
  1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2,
  1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3
]

def certificate (n : ℕ) : ℕ :=
  Array.getD certificates_array (n - 53) 1

lemma cert_valid : ∀ n ∈ Finset.Ico 53 100,
    let k := certificate n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) := by
  decide
