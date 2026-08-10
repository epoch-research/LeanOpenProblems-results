import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A245211: $a(n) = \sum_{d \mid n, d < n} (d \cdot \tau(d))$, where $\tau(d)$ is the number of divisors of $d$.
It is computed as $\left(\sum_{d \mid n} d \cdot \tau(d)\right) - n \cdot \tau(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

/-- A245211 Conjecture: 21 is only number such that a(n) = n. -/
theorem oeis_245211_conjecture_0 : ∀ n : ℕ, 0 < n → (a n = n ↔ n = 21) := by
  sorry
