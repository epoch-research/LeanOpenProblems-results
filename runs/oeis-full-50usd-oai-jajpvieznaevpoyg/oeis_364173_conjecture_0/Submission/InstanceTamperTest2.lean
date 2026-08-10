import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ := 0
local instance instBadPowInt : Pow ℤ ℕ where pow _ _ := 1
example (x y : ℤ) : x ≡ y [ZMOD ((5 : ℤ) ^ (3 : ℕ))] := by
  change x ≡ y [ZMOD (1:ℤ)]
  simp [Int.ModEq]
