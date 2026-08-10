import FormalConjectures.Util.ProblemImports
open Finset Nat Int
#check inferInstanceAs (Decidable (∀ n : ℕ, n ≥ 1 → True))
example : ∀ n : ℕ, n ≥ 1 → True := by native_decide
