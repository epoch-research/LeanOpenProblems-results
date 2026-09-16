import FormalConjectures.Util.ProblemImports

open Nat Real

noncomputable def A217317 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let upper_bound_real : ℝ := (n : ℝ)^2 + (Real.logb 2 n)^2
    let upper_bound_nat : ℕ := Int.toNat (Int.floor upper_bound_real)
    Nat.primeCounting upper_bound_nat - Nat.primeCounting (n^2)

theorem oeis_A217317_conjecture : ∀ n : ℕ, n > 4765516 → A217317 n > 0 := by
  sorry

theorem oeis_A217317_conjecture.disproof : ¬ (type_of% @oeis_A217317_conjecture) := by
  sorry
