import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

lemma lt_pow_self_of_two_le {p r : ℕ} (hp : 2 ≤ p) : r < p ^ r := by
  have h2 : r < 2 ^ r := Nat.lt_two_pow_self
  have hle : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp r
  exact lt_of_lt_of_le h2 hle

example (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : 1 < p := by omega
  have hrne : r ≠ p ^ r := ne_of_lt (lt_pow_self_of_two_le (p:=p) (r:=r) hp2)
  have hrne2 : r ≠ p ^ (r-1) := by
    intro h
    have hlt : p ^ (r-1) < p ^ r := by
      have : r - 1 < r := by omega
      exact Nat.pow_lt_pow_right hp1 this
    rw [← h] at hlt
    exact (not_lt_of_ge (le_of_lt (lt_pow_self_of_two_le (p:=p) (r:=r) hp2))) hlt
  have hpowne : p ^ r ≠ p ^ (r-1) := by
    apply ne_of_gt
    have : r - 1 < r := by omega
    exact Nat.pow_lt_pow_right hp1 this
  have hx0 : (0:ℝ) < (n * p ^ r : ℝ) := by positivity
  have hy0 : (0:ℝ) < (n * p ^ (r-1) : ℝ) := by positivity
  have g1 : 0 < Real.Gamma (3 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g2 : 0 < Real.Gamma (2 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g3 : 0 < Real.Gamma (5 / 3 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Real.Gamma (3 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g5 : 0 < Real.Gamma (2 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g6 : 0 < Real.Gamma (5 / 3 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  grind [a, Nat.ModEq]
