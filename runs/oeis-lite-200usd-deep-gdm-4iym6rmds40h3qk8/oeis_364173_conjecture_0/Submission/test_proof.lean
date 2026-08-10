import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_two : a 2 = 43758 := by
  unfold a
  dsimp
  push_cast
  have h_target : Real.Gamma (9 * (2 : ℝ) + 1) * Real.Gamma (2 * (2 : ℝ) + 1) * Real.Gamma (3 / 2 * (2 : ℝ) + 1) /
    (Real.Gamma (9 / 2 * (2 : ℝ) + 1) * Real.Gamma (4 * (2 : ℝ) + 1) * Real.Gamma (3 * (2 : ℝ) + 1) * Real.Gamma ((2 : ℝ) + 1)) =
    Real.Gamma 19 * Real.Gamma 5 * Real.Gamma 4 / (Real.Gamma 10 * Real.Gamma 9 * Real.Gamma 7 * Real.Gamma 3) := by
    congr 2 <;> norm_num
  rw [h_target]
  have hg19 : Real.Gamma 19 = 6402373705728000 := by
    have : (19 : ℝ) = ↑(18 : ℕ) + 1 := by norm_num
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
  have hg10 : Real.Gamma 10 = 362880 := by
    have : (10 : ℝ) = ↑(9 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg9 : Real.Gamma 9 = 40320 := by
    have : (9 : ℝ) = ↑(8 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg7 : Real.Gamma 7 = 720 := by
    have : (7 : ℝ) = ↑(6 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg3 : Real.Gamma 3 = 2 := by
    have : (3 : ℝ) = ↑(2 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hg19, hg5, hg4, hg10, hg9, hg7, hg3]
  norm_num

theorem a_three : a 3 = 17039360 := by
  unfold a
  dsimp
  push_cast
  have h_target : Real.Gamma (9 * (3 : ℝ) + 1) * Real.Gamma (2 * (3 : ℝ) + 1) * Real.Gamma (3 / 2 * (3 : ℝ) + 1) /
    (Real.Gamma (9 / 2 * (3 : ℝ) + 1) * Real.Gamma (4 * (3 : ℝ) + 1) * Real.Gamma (3 * (3 : ℝ) + 1) * Real.Gamma ((3 : ℝ) + 1)) =
    Real.Gamma 28 * Real.Gamma 7 * Real.Gamma (11 / 2) / (Real.Gamma (29 / 2) * Real.Gamma 13 * Real.Gamma 10 * Real.Gamma 4) := by
    congr 2 <;> norm_num
  rw [h_target]
  have hg28 : Real.Gamma 28 = 10888869450418352160768000000 := by
    have : (28 : ℝ) = ↑(27 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg7 : Real.Gamma 7 = 720 := by
    have : (7 : ℝ) = ↑(6 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg13 : Real.Gamma 13 = 479001600 := by
    have : (13 : ℝ) = ↑(12 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg10 : Real.Gamma 10 = 362880 := by
    have : (10 : ℝ) = ↑(9 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hg4 : Real.Gamma 4 = 6 := by
    have : (4 : ℝ) = ↑(3 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have h1 : (29 / 2 : ℝ) = (27 / 2) + 1 := by norm_num
  have h2 : (27 / 2 : ℝ) = (25 / 2) + 1 := by norm_num
  have h3 : (25 / 2 : ℝ) = (23 / 2) + 1 := by norm_num
  have h4 : (23 / 2 : ℝ) = (21 / 2) + 1 := by norm_num
  have h5 : (21 / 2 : ℝ) = (19 / 2) + 1 := by norm_num
  have h6 : (19 / 2 : ℝ) = (17 / 2) + 1 := by norm_num
  have h7 : (17 / 2 : ℝ) = (15 / 2) + 1 := by norm_num
  have h8 : (15 / 2 : ℝ) = (13 / 2) + 1 := by norm_num
  have h9 : (13 / 2 : ℝ) = (11 / 2) + 1 := by norm_num
  have h_g_29_2 : Real.Gamma (29 / 2) = (27 / 2) * (25 / 2) * (23 / 2) * (21 / 2) * (19 / 2) * (17 / 2) * (15 / 2) * (13 / 2) * (11 / 2) * Real.Gamma (11 / 2) := by
    rw [h1, Real.Gamma_add_one (by norm_num)]
    rw [h2, Real.Gamma_add_one (by norm_num)]
    rw [h3, Real.Gamma_add_one (by norm_num)]
    rw [h4, Real.Gamma_add_one (by norm_num)]
    rw [h5, Real.Gamma_add_one (by norm_num)]
    rw [h6, Real.Gamma_add_one (by norm_num)]
    rw [h7, Real.Gamma_add_one (by norm_num)]
    rw [h8, Real.Gamma_add_one (by norm_num)]
    rw [h9, Real.Gamma_add_one (by norm_num)]
    ring
  rw [hg28, hg7, hg13, hg10, hg4, h_g_29_2]
  have hg_pos : 0 < Real.Gamma (11 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hg_ne : Real.Gamma (11 / 2) ≠ 0 := hg_pos.ne'
  have : 10888869450418352160768000000 * 720 * Real.Gamma (11 / 2) / (((27/2)*(25/2)*(23/2)*(21/2)*(19/2)*(17/2)*(15/2)*(13/2)*(11/2)*Real.Gamma (11/2)) * 479001600 * 362880 * 6) = 17039360 := by
    have : 10888869450418352160768000000 * 720 * Real.Gamma (11 / 2) / (((27 / 2) * (25 / 2) * (23 / 2) * (21 / 2) * (19 / 2) * (17 / 2) * (15 / 2) * (13 / 2) * (11 / 2) * Real.Gamma (11 / 2)) * 479001600 * 362880 * 6) =
           (10888869450418352160768000000 * 720 / (((27 / 2) * (25 / 2) * (23 / 2) * (21 / 2) * (19 / 2) * (17 / 2) * (15 / 2) * (13 / 2) * (11 / 2)) * 479001600 * 362880 * 6)) * (Real.Gamma (11 / 2) / Real.Gamma (11 / 2)) := by
      ring
    rw [this]
    have h_div_self : Real.Gamma (11 / 2) / Real.Gamma (11 / 2) = 1 := div_self hg_ne
    rw [h_div_self]
    norm_num
  exact this
