import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)
#synth Nonempty (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)
#synth Inhabited (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)
