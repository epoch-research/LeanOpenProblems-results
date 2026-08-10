import FormalConjectures.Util.ProblemImports
open Nat
example (n : ℕ) : Decidable (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by infer_instance
example (n : ℕ) : Decidable (Odd n) := by infer_instance
