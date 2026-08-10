import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

example (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := by omega
  have hpr0 : 0 < p ^ r := Nat.pow_pos hp0 r
  have hpr10 : 0 < p ^ (r-1) := Nat.pow_pos hp0 (r-1)
  have hx0 : (0:ℝ) < (n * p ^ r : ℝ) := by positivity
  have hy0 : (0:ℝ) < (n * p ^ (r-1) : ℝ) := by positivity
  grind [a, Nat.ModEq, Real.Gamma_pos_of_pos]
