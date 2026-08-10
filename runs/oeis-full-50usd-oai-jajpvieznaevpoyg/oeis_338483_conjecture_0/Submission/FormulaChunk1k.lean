import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set

def lowersum2 (B p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (B+1))

example : ∀ p, 20000 ≤ p → p < 30000 → Nat.Prime p → Nat.primeCounting' p < lowersum2 1013 p := by
  unfold lowersum2
  native_decide
