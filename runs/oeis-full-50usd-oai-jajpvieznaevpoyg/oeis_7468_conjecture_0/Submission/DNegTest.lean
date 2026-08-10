import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

example : (¬¬(∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)) → ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  exact Classical.byContradiction

example : ¬¬(∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) := by
  intro h
  push_neg at h
  rcases h with ⟨n, hn, hs, hne⟩
  -- no contradiction is available
  guard_target = False
  sorry
