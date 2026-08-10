import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_one : a 1 = 128 := by
  unfold a
  dsimp
  -- arguments for n = 1:
  -- 9*n_r + 1 = 10
  -- 2*n_r + 1 = 3
  -- 3/2*n_r + 1 = 5/2
  -- 9/2*n_r + 1 = 11/2
  -- 4*n_r + 1 = 5
  -- 3*n_r + 1 = 4
  -- n_r + 1 = 2
  have h1 : Real.Gamma (9 * (1 : ℝ) + 1) = Nat.factorial 9 := by
    have : 9 * (1 : ℝ) + 1 = 10 := by norm_num
    rw [this, Real.Gamma_ofNat_eq_factorial]
  have h2 : Real.Gamma (2 * (1 : ℝ) + 1) = Nat.factorial 2 := by
    have : 2 * (1 : ℝ) + 1 = 3 := by norm_num
    rw [this, Real.Gamma_ofNat_eq_factorial]
  have h4 : Real.Gamma (4 * (1 : ℝ) + 1) = Nat.factorial 4 := by
    have : 4 * (1 : ℝ) + 1 = 5 := by norm_num
    rw [this, Real.Gamma_ofNat_eq_factorial]
  have h5 : Real.Gamma (3 * (1 : ℝ) + 1) = Nat.factorial 3 := by
    have : 3 * (1 : ℝ) + 1 = 4 := by norm_num
    rw [this, Real.Gamma_ofNat_eq_factorial]
  have h6 : Real.Gamma ((1 : ℝ) + 1) = Nat.factorial 1 := by
    have : (1 : ℝ) + 1 = 2 := by norm_num
    rw [this, Real.Gamma_ofNat_eq_factorial]
  
  -- now we need Real.Gamma (5/2) and Real.Gamma (11/2)
  -- Real.Gamma (5/2) = 3/2 * 1/2 * Real.Gamma (1/2)
  have h3 : Real.Gamma (5/2) = 3/4 * Real.Gamma (1/2) := by
    have h3_1 : Real.Gamma (3/2 + 1) = 3/2 * Real.Gamma (3/2) := Real.Gamma_add_one (by norm_num)
    have h3_2 : Real.Gamma (1/2 + 1) = 1/2 * Real.Gamma (1/2) := Real.Gamma_add_one (by norm_num)
    have : (5/2 : ℝ) = 3/2 + 1 := by norm_num
    rw [this, h3_1]
    have : (3/2 : ℝ) = 1/2 + 1 := by norm_num
    rw [this, h3_2]
    ring

  -- Real.Gamma (11/2) = 9/2 * 7/2 * 5/2 * 3/4 * Real.Gamma (1/2) = 945/32 * Real.Gamma (1/2)
  have h7 : Real.Gamma (11/2) = 945/32 * Real.Gamma (1/2) := by
    have h7_1 : Real.Gamma (9/2 + 1) = 9/2 * Real.Gamma (9/2) := Real.Gamma_add_one (by norm_num)
    have h7_2 : Real.Gamma (7/2 + 1) = 7/2 * Real.Gamma (7/2) := Real.Gamma_add_one (by norm_num)
    have h7_3 : Real.Gamma (5/2 + 1) = 5/2 * Real.Gamma (5/2) := Real.Gamma_add_one (by norm_num)
    have : (11/2 : ℝ) = 9/2 + 1 := by norm_num
    rw [this, h7_1]
    have : (9/2 : ℝ) = 7/2 + 1 := by norm_num
    rw [this, h7_2]
    have : (7/2 : ℝ) = 5/2 + 1 := by norm_num
    rw [this, h7_3]
    rw [h3]
    ring

  have h_ne_zero : Real.Gamma (1/2) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m
    intro h_eq
    have : (1/2 : ℝ) > 0 := by norm_num
    have : -↑m ≤ (0 : ℝ) := by
      push_cast
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    linarith

  have h_arg1 : 9 * (1 : ℝ) + 1 = 10 := by norm_num
  have h_arg2 : 2 * (1 : ℝ) + 1 = 3 := by norm_num
  have h_arg3 : 3 / 2 * (1 : ℝ) + 1 = 5 / 2 := by norm_num
  have h_arg4 : 9 / 2 * (1 : ℝ) + 1 = 11 / 2 := by norm_num
  have h_arg5 : 4 * (1 : ℝ) + 1 = 5 := by norm_num
  have h_arg6 : 3 * (1 : ℝ) + 1 = 4 := by norm_num
  have h_arg7 : (1 : ℝ) + 1 = 2 := by norm_num
  push_cast
  rw [h_arg3, h_arg4]
  rw [h1, h2, h3, h7, h4, h5, h6]
  
  -- Now simplify the fraction
  -- numerator is (factorial 9 * factorial 2 * (3/4 * Gamma (1/2)))
  -- denominator is ((945/32 * Gamma (1/2)) * factorial 4 * factorial 3 * factorial 1)
  -- Since Gamma (1/2) is non-zero, we can cancel it.
  -- Let's do this by using field_simp or ring.
  have h_num : (Nat.factorial 9 : ℝ) * (Nat.factorial 2 : ℝ) * (3/4 * Real.Gamma (1/2)) = 544320 * Real.Gamma (1/2) := by
    -- factorial 9 = 362880, factorial 2 = 2.
    -- 362880 * 2 * 3/4 = 544320.
    have : (Nat.factorial 9 : ℝ) = 362880 := by rfl
    have : (Nat.factorial 2 : ℝ) = 2 := by rfl
    rw [this]
    ring
  
  have h_den : (945/32 * Real.Gamma (1/2)) * (Nat.factorial 4 : ℝ) * (Nat.factorial 3 : ℝ) * (Nat.factorial 1 : ℝ) = 4252.5 * Real.Gamma (1/2) := by
    have : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    have : (Nat.factorial 3 : ℝ) = 6 := by norm_num
    have : (Nat.factorial 1 : ℝ) = 1 := by norm_num
    rw [this]
    ring

  rw [h_num, h_den]
  -- Now we have: 544320 * Gamma (1/2) / (4252.5 * Gamma (1/2)) = 128
  rw [mul_div_mul_right _ _ h_ne_zero]
  norm_num
