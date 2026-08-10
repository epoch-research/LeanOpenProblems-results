import FormalConjectures.Util.ProblemImports
open Real Nat Int
open scoped BigOperators
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

example (p n : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p) (hn : 0 < n) :
    a (n * p) ≡ a n [MOD p ^ 3] := by
  have hp1 : 1 < p := by omega
  have hp0 : 0 < p := by omega
  -- no known path
  exact?
