import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

theorem t (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : 1 < p := by omega
  have hpred : r - 1 < r := by omega
  have hpowlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp1 hpred
  have hpowne : p ^ r ≠ p ^ (r - 1) := ne_of_gt hpowlt
  have hpowne' : (p ^ (r - 1) : ℕ) ≠ p ^ r := ne_of_lt hpowlt
  have hmulne : n * p ^ r ≠ n * p ^ (r - 1) := by
    intro h
    have hc := Nat.mul_right_cancel₀ (ne_of_gt hn) h
    exact hpowne hc
  have hmulne' : n * p ^ (r - 1) ≠ n * p ^ r := fun h => hmulne h.symm
  have hrne : r ≠ p ^ r := by
    have h2 : r < 2 ^ r := Nat.lt_two_pow_self
    have hle : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp2 r
    exact ne_of_lt (lt_of_lt_of_le h2 hle)
  have hrne2 : r ≠ p ^ (r - 1) := by
    intro h
    rw [← h] at hpowlt
    exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hp2 r)))) hpowlt
  have hx0 : (0:ℝ) < (n * p ^ r : ℝ) := by positivity
  have hy0 : (0:ℝ) < (n * p ^ (r-1) : ℝ) := by positivity
  have g1 : 0 < Real.Gamma (3 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g2 : 0 < Real.Gamma (2 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g3 : 0 < Real.Gamma (5 / 3 * (↑n * ↑p ^ r) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Real.Gamma (3 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g5 : 0 < Real.Gamma (2 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have g6 : 0 < Real.Gamma (5 / 3 * (↑n * ↑p ^ (r-1)) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have dpos1 : 0 < Real.Gamma (3 * (↑n * ↑p ^ r) + 1) * Real.Gamma (2 * (↑n * ↑p ^ r) + 1) * Real.Gamma (5 / 3 * (↑n * ↑p ^ r) + 1) := by positivity
  have dpos2 : 0 < Real.Gamma (3 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (2 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (5 / 3 * (↑n * ↑p ^ (r-1)) + 1) := by positivity
  have numpos1 : 0 < Real.Gamma (6 * (↑n * ↑p ^ r) + 1) * Real.Gamma (2 / 3 * (↑n * ↑p ^ r) + 1) := by positivity
  have numpos2 : 0 < Real.Gamma (6 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (2 / 3 * (↑n * ↑p ^ (r-1)) + 1) := by positivity
  have valpos1 : 0 < (Real.Gamma (6 * (↑n * ↑p ^ r) + 1) * Real.Gamma (2 / 3 * (↑n * ↑p ^ r) + 1)) / (Real.Gamma (3 * (↑n * ↑p ^ r) + 1) * Real.Gamma (2 * (↑n * ↑p ^ r) + 1) * Real.Gamma (5 / 3 * (↑n * ↑p ^ r) + 1)) := by positivity
  have valpos2 : 0 < (Real.Gamma (6 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (2 / 3 * (↑n * ↑p ^ (r-1)) + 1)) / (Real.Gamma (3 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (2 * (↑n * ↑p ^ (r-1)) + 1) * Real.Gamma (5 / 3 * (↑n * ↑p ^ (r-1)) + 1)) := by positivity
  grind [a, Nat.ModEq]
