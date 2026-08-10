import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def lowersum3 (B p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (r + 1))

example : ∀ p < 100000, Nat.Prime p → p > 31 →
    Nat.primeCounting' p < lowersum3 1013 p := by
  unfold lowersum3
  native_decide
