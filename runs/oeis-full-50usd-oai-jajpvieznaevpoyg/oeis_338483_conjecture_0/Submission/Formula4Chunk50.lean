import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def lowersum4 (B C p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (r + 1))
  + ((Finset.Icc 2 C).filter (fun q => Nat.Prime q ∧ q^3 < p)).card

example : ∀ p, 10000 ≤ p → p < 50000 → Nat.Prime p → p > 31 →
    Nat.primeCounting' p < lowersum4 11 40 p := by
  unfold lowersum4
  native_decide
