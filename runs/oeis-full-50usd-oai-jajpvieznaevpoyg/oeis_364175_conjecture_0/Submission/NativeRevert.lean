import FormalConjectures.Util.ProblemImports
example (x : ℕ) : x = x := by native_decide +revert
-- example (x y : ℕ) : x = y := by native_decide +revert
noncomputable def f (n : ℕ) : ℕ := Classical.choice (show Nonempty ℕ from ⟨0⟩)
example (x : ℕ) : f x = f x := by native_decide +revert
