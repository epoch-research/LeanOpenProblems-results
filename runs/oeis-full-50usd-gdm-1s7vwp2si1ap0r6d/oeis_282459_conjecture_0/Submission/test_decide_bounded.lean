import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def certificate (n : ℕ) : ℕ :=
  if n < 100 then 1 else 2

lemma cert_valid : ∀ n, 53 ≤ n ∧ n < 100 →
    1 ≤ certificate n ∧ certificate n ≤ log 2 (2 * n + 1) := by
  decide
