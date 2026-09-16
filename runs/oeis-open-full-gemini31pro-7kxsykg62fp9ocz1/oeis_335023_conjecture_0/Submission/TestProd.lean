import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

theorem test : P_def 2 20000 > 0 := by decide
