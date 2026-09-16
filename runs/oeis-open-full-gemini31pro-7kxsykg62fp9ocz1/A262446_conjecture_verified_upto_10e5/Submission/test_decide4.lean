import FormalConjectures.Util.ProblemImports
open Nat Finset

def A262439 (n : ℕ) : ℕ := primeCounting (n * (n + 1) / 2 + 1)
def A262446 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k => (Ico (k + 1) n).sum fun m =>
    if A262439 n = A262439 k + A262439 m then 1 else 0

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

theorem test50 : A262446 50 > 0 := by decide
