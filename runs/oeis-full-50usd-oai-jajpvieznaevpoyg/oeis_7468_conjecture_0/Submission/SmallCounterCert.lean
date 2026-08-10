import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

-- n=38 known square, demonstrate proof of a 38 = 456^2 with native_decide? not allowed final, but test.
example : IsSquare (a 38) := by
  use 456
  -- use nth_count facts? try native first
  native_decide
#print axioms _example
