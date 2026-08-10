import FormalConjectures.Util.ProblemImports
open Finset Nat

example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p % 4 = 3) :
    0 ≤ ∑ a ∈ Finset.Ico 1 (p / 2 + 1), legendreSym p (a : ℤ) := by
  exact?

example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p % 4 = 3) :
    0 ≤ ∑ a in Finset.Ico 1 (p / 2 + 1), legendreSym p (a : ℤ) := by
  aesop?
