import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem choose_eq_of_cast (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) {m : ℕ} {z : ℤ}
    (hz : (z : ℝ) = a m) : Classical.choose (h_int m) = z := by
  have hc := Classical.choose_spec (h_int m)
  exact (Int.cast_injective (α := ℝ)) (hc.trans hz.symm)
#print axioms choose_eq_of_cast
