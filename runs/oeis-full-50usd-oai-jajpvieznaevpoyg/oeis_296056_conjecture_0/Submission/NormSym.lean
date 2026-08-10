import FormalConjectures.Util.ProblemImports
open Nat

noncomputable def Rrat (n : ℕ) : ℚ :=
  ((4*n-4)! : ℚ) * ((4*n-6)! : ℚ) * ((n-3)! : ℚ) * ((n-2)! : ℚ) /
  (12 * ((n)! : ℚ) * ((n-1)! : ℚ) * ((2*n-6)! : ℚ) * ((2*n-4)! : ℚ) * ((2*n-3)! : ℚ) * ((2*n-2)! : ℚ))

example (n : ℕ) : Rrat n ∈ Set.range (Int.cast : ℤ → ℚ) := by
  unfold Rrat
  norm_num
