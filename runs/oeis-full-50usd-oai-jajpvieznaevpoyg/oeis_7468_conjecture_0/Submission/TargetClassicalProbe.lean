import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

set_option pp.all true in
#check (Classical.propComplete (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38))

example : (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) ∨
    ¬ (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) := Classical.em _
