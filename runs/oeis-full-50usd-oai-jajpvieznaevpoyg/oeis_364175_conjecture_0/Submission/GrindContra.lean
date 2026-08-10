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
  have hp1 : 1 < p := by omega
  have hx0 : (0:ℝ) < (n * p ^ r : ℝ) := by positivity
  have hy0 : (0:ℝ) < (n * p ^ (r-1) : ℝ) := by positivity
  have den1pos : 0 < Real.Gamma (3 * (↑n * ↑p ^ r) + 1) * Real.Gamma (2 * (↑n * ↑p ^ r) + 1) * Real.Gamma (5 * 3⁻¹ * (↑n * ↑p ^ r) + 1) := by
    apply mul_pos
    · apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity
    · apply Real.Gamma_pos_of_pos; positivity
  have den2pos : 0 < Real.Gamma (3 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (2 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (5 * 3⁻¹ * (↑n * ↑p ^ (r-1)) + 1) := by
    apply mul_pos
    · apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity
    · apply Real.Gamma_pos_of_pos; positivity
  have hrne : r ≠ p ^ r := by
    have h2 : r < 2 ^ r := Nat.lt_two_pow_self
    have hle : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left (by omega : 2 ≤ p) r
    exact Nat.ne_of_lt (lt_of_lt_of_le h2 hle)
  by_contra h
  grind [a, Nat.ModEq]
