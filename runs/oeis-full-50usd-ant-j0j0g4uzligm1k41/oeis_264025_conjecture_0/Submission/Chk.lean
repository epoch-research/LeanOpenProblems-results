import FormalConjectures.Util.ProblemImports
open Nat
def reps (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      Finset.range ((2 * n).sqrt + 1)).filter
    (fun p => p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
      (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1)))
-- Lean's own check: a(n) >= 2 for all n in [1345, 60000]
example : ∀ n ∈ Finset.Icc 1345 60000, 2 ≤ (reps n).card := by native_decide
