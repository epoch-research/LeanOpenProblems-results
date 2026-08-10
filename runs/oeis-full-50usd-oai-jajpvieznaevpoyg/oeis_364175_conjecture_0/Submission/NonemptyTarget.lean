import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat
#check (inferInstance : Nonempty (∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r → a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)]))
