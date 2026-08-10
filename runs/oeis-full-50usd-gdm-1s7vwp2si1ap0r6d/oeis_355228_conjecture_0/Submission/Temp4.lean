import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma test_fast : ∀ x < 180, x ≠ 120 ∧ x ≠ 144 ∧ x ≠ 168 → (Nat.divisors x).card < 14 ∨ (Nat.divisors x).sum id < 2 * x := by decide
