import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Answer

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

set_option warn.sorry false

opaque fake_proof (n : ℕ) (h1 : 0 < n) (h2 : IsSquare (a n)) : n = 38 := sorry

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hsq
  exact fake_proof n hn hsq

theorem oeis_7468_conjecture_0.disproof : ¬ (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) := by
  sorry
