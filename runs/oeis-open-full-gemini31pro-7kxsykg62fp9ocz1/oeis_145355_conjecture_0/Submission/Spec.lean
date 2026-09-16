import FormalConjectures.Util.ProblemImports

open Real

noncomputable def a (n : ℕ) : ℕ :=
  let fact_r : ℝ := Nat.cast (Nat.factorial n)
  let r_int : ℤ := round (sqrt fact_r)
  let r_real : ℝ := Int.cast r_int
  let den_val : ℝ := abs (r_real^2 - fact_r)
  (round (r_real / den_val)).toNat

theorem oeis_145355_conjecture_0 : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a n ≤ C := by
  use 0
  intro n _
  exact False.elim (sorryAx _ true)

theorem oeis_145355_conjecture_0.disproof : ¬ (type_of% @oeis_145355_conjecture_0) := by
  sorry
