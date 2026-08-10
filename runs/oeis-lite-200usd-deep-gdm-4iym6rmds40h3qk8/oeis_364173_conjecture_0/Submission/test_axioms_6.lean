import Mathlib

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_one : a 1 = 128 := by
  unfold a
  dsimp
  have h_target : Real.Gamma (9 * (1 : ℝ) + 1) * Real.Gamma (2 * (1 : ℝ) + 1) * Real.Gamma (3 / 2 * (1 : ℝ) + 1) /
    (Real.Gamma (9 / 2 * (1 : ℝ) + 1) * Real.Gamma (4 * (1 : ℝ) + 1) * Real.Gamma (3 * (1 : ℝ) + 1) * Real.Gamma ((1 : ℝ) + 1)) =
    Real.Gamma 10 * Real.Gamma 3 * Real.Gamma (5 / 2) / (Real.Gamma (11 / 2) * Real.Gamma 5 * Real.Gamma 4 * Real.Gamma 2) := by
    congr 2 <;> norm_num
  push_cast
  rw [h_target]
  have hg10 : Real.Gamma 10 = 362880 := by
    have : (10 : ℝ) = ↑(9 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg3 : Real.Gamma 3 = 2 := by
    have : (3 : ℝ) = ↑(2 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg5 : Real.Gamma 5 = 24 := by
    have : (5 : ℝ) = ↑(4 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg4 : Real.Gamma 4 = 6 := by
    have : (4 : ℝ) = ↑(3 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg2 : Real.Gamma 2 = 1 := by
    have : (2 : ℝ) = ↑(1 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have h1 : (11 / 2 : ℝ) = (9 / 2) + 1 := by norm_num
  have h2 : (9 / 2 : ℝ) = (7 / 2) + 1 := by norm_num
  have h3 : (7 / 2 : ℝ) = (5 / 2) + 1 := by norm_num
  have h_g_11_2 : Real.Gamma (11 / 2) = (9 / 2) * (7 / 2) * (5 / 2) * Real.Gamma (5 / 2) := by
    rw [h1, Real.Gamma_add_one (by norm_num)]
    rw [h2, Real.Gamma_add_one (by norm_num)]
    rw [h3, Real.Gamma_add_one (by norm_num)]
    ring
  rw [hg10, hg3, hg5, hg4, hg2, h_g_11_2]
  have hg_pos : 0 < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hg_ne : Real.Gamma (5 / 2) ≠ 0 := hg_pos.ne'
  have h_cancel : 362880 * 2 * Real.Gamma (5 / 2) / ((9 / 2 * (7 / 2) * (5 / 2) * Real.Gamma (5 / 2)) * 24 * 6 * 1) = 128 := by
    have : 362880 * 2 * Real.Gamma (5 / 2) / ((9 / 2 * (7 / 2) * (5 / 2) * Real.Gamma (5 / 2)) * 24 * 6 * 1) =
           (362880 * 2 / ((9 / 2 * (7 / 2) * (5 / 2)) * 24 * 6 * 1)) * (Real.Gamma (5 / 2) / Real.Gamma (5 / 2)) := by
      ring
    rw [this]
    have h_div_self : Real.Gamma (5 / 2) / Real.Gamma (5 / 2) = 1 := div_self hg_ne
    rw [h_div_self]
    norm_num
  exact h_cancel

#print axioms a_one
