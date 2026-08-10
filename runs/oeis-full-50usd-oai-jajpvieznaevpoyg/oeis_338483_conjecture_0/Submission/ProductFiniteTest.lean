import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set

def prodSet (B p : ℕ) : Finset ℕ :=
  (((Finset.Icc 2 B).filter Nat.Prime).biUnion fun r =>
    (((Finset.Ico 2 p).filter (fun q => Nat.Prime q ∧ q ≠ r ∧ r * q < p)).image (fun q => r * q))) ∪
  (((Finset.Ico 2 p).filter (fun r => Nat.Prime r ∧ r^3 < p)).image (fun r => r^3))

example : ∀ p < 1000, Nat.Prime p → p > 31 → Nat.primeCounting' p < (prodSet 1013 p).card := by
  unfold prodSet
  native_decide
