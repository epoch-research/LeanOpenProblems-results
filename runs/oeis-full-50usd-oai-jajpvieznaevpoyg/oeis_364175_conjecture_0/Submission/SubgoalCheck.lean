import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat
example (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r) : p ^ (3*r) ≠ 1 := by
  have hp2 : 2 ≤ p := by omega
  have hpos : 0 < 3*r := by omega
  have : 1 < p ^ (3*r) := Nat.one_lt_pow hpos (by omega)
  omega
example (m x y : ℕ) (hm : m = 1) : x ≡ y [MOD m] := by simp [Nat.ModEq, hm]
