import FormalConjectures.Util.ProblemImports

open Nat Finset

def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

def a (n : ℕ) : ℕ := A331343 n

theorem oeis_331343_conjecture_0 : ∀ n : ℕ, n > 3 → n ^ 3 ∣ (a n) → Nat.Prime n := by
  sorry

theorem oeis_331343_conjecture_0.disproof : ¬ (type_of% @oeis_331343_conjecture_0) := by
  sorry
