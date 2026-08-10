import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example (h_int : ∀ m : ℕ, a m ∈ Set.range (fun x : ℤ => (x : ℝ))) {m : ℕ} {z : ℤ}
    (hz : (z : ℝ) = a m) : Classical.choose (h_int m) = z := by
  have hc := Classical.choose_spec (h_int m)
  exact (Int.cast_injective (α := ℝ)) (hc.trans hz.symm)

example (h_int : ∀ m : ℕ, a m ∈ Set.range (fun x : ℤ => (x : ℝ))) {m₁ m₂ : ℕ}
    (hval : a m₁ = a m₂) : Classical.choose (h_int m₁) = Classical.choose (h_int m₂) := by
  apply (Int.cast_injective (α := ℝ))
  calc
    ((Classical.choose (h_int m₁) : ℤ) : ℝ) = a m₁ := Classical.choose_spec (h_int m₁)
    _ = a m₂ := hval
    _ = ((Classical.choose (h_int m₂) : ℤ) : ℝ) := (Classical.choose_spec (h_int m₂)).symm
