import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range n
  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by sorry
theorem oeis_a389790_conjecture_1.disproof : ¬ (∀ n : ℕ, 474 ≤ n → 0 < a n) := by sorry
