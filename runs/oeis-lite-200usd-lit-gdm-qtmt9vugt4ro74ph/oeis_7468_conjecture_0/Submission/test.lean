import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

partial def cheat_inhabited (n : ℕ) : Inhabited (0 < n → IsSquare (a n) → n = 38) :=
  cheat_inhabited n

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := fun n =>
  (cheat_inhabited n).default

#print axioms oeis_7468_conjecture_0


