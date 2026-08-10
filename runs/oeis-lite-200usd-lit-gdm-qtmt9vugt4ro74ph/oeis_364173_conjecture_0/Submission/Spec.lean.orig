import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_two_eq_43758 : a 2 = 43758 := by
  dsimp [a]
  push_cast
  have h9 : (9 : ℝ) * 2 + 1 = 19 := by norm_num
  have h2 : (2 : ℝ) * 2 + 1 = 5 := by norm_num
  have h32 : (3 / 2 : ℝ) * 2 + 1 = 4 := by norm_num
  have h92 : (9 / 2 : ℝ) * 2 + 1 = 10 := by norm_num
  have h4 : (4 : ℝ) * 2 + 1 = 9 := by norm_num
  have h3 : (3 : ℝ) * 2 + 1 = 7 := by norm_num
  have h1 : (2 : ℝ) + 1 = 3 := by norm_num
  rw [h9, h2, h32, h92, h4, h3, h1]
  -- Now rewrite everything using Real.Gamma_nat_eq_factorial
  have h_g19 : Real.Gamma 19 = Nat.factorial 18 := by
    have : (19 : ℝ) = ↑(18 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 18]
  have h_g5 : Real.Gamma 5 = Nat.factorial 4 := by
    have : (5 : ℝ) = ↑(4 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 4]
  have h_g4 : Real.Gamma 4 = Nat.factorial 3 := by
    have : (4 : ℝ) = ↑(3 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 3]
  have h_g10 : Real.Gamma 10 = Nat.factorial 9 := by
    have : (10 : ℝ) = ↑(9 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 9]
  have h_g9 : Real.Gamma 9 = Nat.factorial 8 := by
    have : (9 : ℝ) = ↑(8 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 8]
  have h_g7 : Real.Gamma 7 = Nat.factorial 6 := by
    have : (7 : ℝ) = ↑(6 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 6]
  have h_g3 : Real.Gamma 3 = Nat.factorial 2 := by
    have : (3 : ℝ) = ↑(2 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 2]
  rw [h_g19, h_g5, h_g4, h_g10, h_g9, h_g7, h_g3]
  norm_num


theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  sorry




theorem test_gamma_add_one : Real.Gamma (29 / 2) = (27 / 2) * Real.Gamma (27 / 2) := by
  have h : (29 / 2 : ℝ) = 27 / 2 + 1 := by norm_num
  rw [h]
  exact Real.Gamma_add_one (by norm_num)


theorem a_three_eq_17039360 : a 3 = 17039360 := by
  dsimp [a]
  push_cast
  have h9 : (9 : ℝ) * 3 + 1 = 28 := by norm_num
  have h2 : (2 : ℝ) * 3 + 1 = 7 := by norm_num
  have h32 : (3 / 2 : ℝ) * 3 + 1 = 11 / 2 := by norm_num
  have h92 : (9 / 2 : ℝ) * 3 + 1 = 29 / 2 := by norm_num
  have h4 : (4 : ℝ) * 3 + 1 = 13 := by norm_num
  have h3 : (3 : ℝ) * 3 + 1 = 10 := by norm_num
  have h1 : (3 : ℝ) + 1 = 4 := by norm_num
  rw [h9, h2, h32, h92, h4, h3, h1]
  -- Rewrite Gamma (29 / 2) in terms of Gamma (11 / 2)
  have h_29_2 : (29 / 2 : ℝ) = 27 / 2 + 1 := by norm_num
  have h_27_2 : (27 / 2 : ℝ) = 25 / 2 + 1 := by norm_num
  have h_25_2 : (25 / 2 : ℝ) = 23 / 2 + 1 := by norm_num
  have h_23_2 : (23 / 2 : ℝ) = 21 / 2 + 1 := by norm_num
  have h_21_2 : (21 / 2 : ℝ) = 19 / 2 + 1 := by norm_num
  have h_19_2 : (19 / 2 : ℝ) = 17 / 2 + 1 := by norm_num
  have h_17_2 : (17 / 2 : ℝ) = 15 / 2 + 1 := by norm_num
  have h_15_2 : (15 / 2 : ℝ) = 13 / 2 + 1 := by norm_num
  have h_13_2 : (13 / 2 : ℝ) = 11 / 2 + 1 := by norm_num
  rw [h_29_2, Real.Gamma_add_one (by norm_num)]
  rw [h_27_2, Real.Gamma_add_one (by norm_num)]
  rw [h_25_2, Real.Gamma_add_one (by norm_num)]
  rw [h_23_2, Real.Gamma_add_one (by norm_num)]
  rw [h_21_2, Real.Gamma_add_one (by norm_num)]
  rw [h_19_2, Real.Gamma_add_one (by norm_num)]
  rw [h_17_2, Real.Gamma_add_one (by norm_num)]
  rw [h_15_2, Real.Gamma_add_one (by norm_num)]
  rw [h_13_2, Real.Gamma_add_one (by norm_num)]
  -- Now cancel Gamma (11 / 2)
  have h_g_pos : 0 < Real.Gamma (11 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have h_g_ne : Real.Gamma (11 / 2) ≠ 0 := ne_of_gt h_g_pos
  -- Rewrite other Gamma terms using factorial
  have h_g28 : Real.Gamma 28 = Nat.factorial 27 := by
    have : (28 : ℝ) = ↑(27 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 27]
  have h_g7 : Real.Gamma 7 = Nat.factorial 6 := by
    have : (7 : ℝ) = ↑(6 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 6]
  have h_g13 : Real.Gamma 13 = Nat.factorial 12 := by
    have : (13 : ℝ) = ↑(12 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 12]
  have h_g10 : Real.Gamma 10 = Nat.factorial 9 := by
    have : (10 : ℝ) = ↑(9 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 9]
  have h_g4 : Real.Gamma 4 = Nat.factorial 3 := by
    have : (4 : ℝ) = ↑(3 + 1 : ℕ) := by norm_num
    rw [this, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial 3]
  rw [h_g28, h_g7, h_g13, h_g10, h_g4]
  -- Now we simplify the additions
  have h_add1 : (11 / 2 : ℝ) + 1 = 13 / 2 := by norm_num
  have h_add2 : (13 / 2 : ℝ) + 1 = 15 / 2 := by norm_num
  have h_add3 : (15 / 2 : ℝ) + 1 = 17 / 2 := by norm_num
  have h_add4 : (17 / 2 : ℝ) + 1 = 19 / 2 := by norm_num
  have h_add5 : (19 / 2 : ℝ) + 1 = 21 / 2 := by norm_num
  have h_add6 : (21 / 2 : ℝ) + 1 = 23 / 2 := by norm_num
  have h_add7 : (23 / 2 : ℝ) + 1 = 25 / 2 := by norm_num
  have h_add8 : (25 / 2 : ℝ) + 1 = 27 / 2 := by norm_num
  rw [h_add1, h_add2, h_add3, h_add4, h_add5, h_add6, h_add7, h_add8]
  -- Now simplify multiplication and cancel Gamma (11 / 2)
  -- The numerator has: Nat.factorial 27 * Nat.factorial 6 * Real.Gamma (11 / 2)
  -- Let's group the denominator
  have h_eq : ((Nat.factorial 27 * Nat.factorial 6 : ℝ) * Real.Gamma (11 / 2)) /
    ((27 / 2 * (25 / 2 * (23 / 2 * (21 / 2 * (19 / 2 * (17 / 2 * (15 / 2 * (13 / 2 * (11 / 2 * Real.Gamma (11 / 2)))))))))) * (Nat.factorial 12 : ℝ) * (Nat.factorial 9 : ℝ) * (Nat.factorial 3 : ℝ)) = 17039360 := by
    calc
      ((Nat.factorial 27 * Nat.factorial 6 : ℝ) * Real.Gamma (11 / 2)) /
    ((27 / 2 * (25 / 2 * (23 / 2 * (21 / 2 * (19 / 2 * (17 / 2 * (15 / 2 * (13 / 2 * (11 / 2 * Real.Gamma (11 / 2)))))))))) * (Nat.factorial 12 : ℝ) * (Nat.factorial 9 : ℝ) * (Nat.factorial 3 : ℝ))
      _ = ( (Nat.factorial 27 * Nat.factorial 6 : ℝ) * Real.Gamma (11 / 2) ) / ( ( (27/2 * 25/2 * 23/2 * 21/2 * 19/2 * 17/2 * 15/2 * 13/2 * 11/2 * Nat.factorial 12 * Nat.factorial 9 * Nat.factorial 3 : ℝ) ) * Real.Gamma (11 / 2) ) := by
        congr 1
        ring
      _ = (Nat.factorial 27 * Nat.factorial 6 : ℝ) / (27/2 * 25/2 * 23/2 * 21/2 * 19/2 * 17/2 * 15/2 * 13/2 * 11/2 * Nat.factorial 12 * Nat.factorial 9 * Nat.factorial 3 : ℝ) := by
        rw [mul_div_mul_right _ _ h_g_ne]
      _ = 17039360 := by
        norm_num
  exact h_eq

