import FormalConjectures.Util.ProblemImports

example (p r : ℕ) (a b : ℤ) : a ≡ b [ZMOD ((p : ℤ) ^ (3 * r))] := by
  letI : Pow ℤ ℕ := ⟨fun _ _ => 1⟩
  -- should not simplify, target already elaborated with global pow
  simp [Int.ModEq]
