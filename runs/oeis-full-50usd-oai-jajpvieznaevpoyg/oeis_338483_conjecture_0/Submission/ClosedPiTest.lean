import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def lowerSemi (B p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (r + 1))

example : Nat.primeCounting' 10000000 = 664579 := by native_decide
example : lowerSemi 1013 10000000 = 1792476 := by native_decide
