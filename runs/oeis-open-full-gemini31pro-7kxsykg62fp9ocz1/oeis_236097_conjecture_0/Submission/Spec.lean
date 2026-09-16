import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

noncomputable def A236097 (n : ℕ) : ℕ :=
  (Icc 1 (n - 3)).sum fun k =>
    let p_val := k.totient + (n - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0

theorem oeis_236097_conjecture_0 : ∀ (n : ℕ), n > 31 → A236097 n > 0 := by
  sorry

theorem oeis_236097_conjecture_0.disproof : ¬ (type_of% @oeis_236097_conjecture_0) := by
  sorry
