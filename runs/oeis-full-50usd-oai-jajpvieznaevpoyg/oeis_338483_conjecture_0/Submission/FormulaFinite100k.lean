import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set

def lowersum (B p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum (fun r => Nat.primeCounting' ((p + r - 1) / r))

example : ∀ p < 100000, Nat.Prime p → p > 31 → Nat.primeCounting' p < lowersum 1013 p := by
  unfold lowersum
  native_decide
