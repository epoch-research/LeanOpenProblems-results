import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma divisors_120_eq : (Nat.divisors 120) = ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} : Finset ℕ) := by decide
lemma divisors_144_eq : (Nat.divisors 144) = ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by decide
lemma divisors_168_eq : (Nat.divisors 168) = ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by decide
