import FormalConjectures.Util.ProblemImports

open Real Nat

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n.cast
  let num_int_15 : ℝ := (15 * n).factorial.cast
  let num_int_2 : ℝ := (2 * n).factorial.cast
  let num_frac_5_halves : ℝ := Real.Gamma (5 * n_r / 2 + 1)

  let den_frac_15_halves : ℝ := Real.Gamma (15 * n_r / 2 + 1)
  let den_int_6 : ℝ := (6 * n).factorial.cast
  let den_int_5 : ℝ := (5 * n).factorial.cast
  let den_int_1 : ℝ := n.factorial.cast

  (num_int_15 * num_frac_5_halves * num_int_2) /
  (den_frac_15_halves * den_int_6 * den_int_5 * den_int_1)

lemma real_div_range_int_cast (a b : ℤ) (hb : b ≠ 0) :
  (a : ℝ) / (b : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) ↔ b ∣ a := by
  constructor
  · rintro ⟨c, hc⟩
    use c
    have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have h_eq : (a : ℝ) = (b : ℝ) * (c : ℝ) := by
      rw [hc, mul_div_cancel₀ (a : ℝ) hb_real]
    have h_eq2 : (a : ℝ) = ((b * c : ℤ) : ℝ) := by
      rw [Int.cast_mul]
      exact h_eq
    exact_mod_cast h_eq2
  · rintro ⟨c, rfl⟩
    use c
    have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    rw [Int.cast_mul]
    exact (mul_div_cancel_left₀ (c : ℝ) hb_real).symm

lemma a_even (m : ℕ) : a (2 * m) =
  (((30 * m).factorial : ℝ) * ((5 * m).factorial : ℝ) * ((4 * m).factorial : ℝ)) /
  (((15 * m).factorial : ℝ) * ((12 * m).factorial : ℝ) * ((10 * m).factorial : ℝ) * ((2 * m).factorial : ℝ)) := by
  dsimp [a]
  -- We need to simplify the Gamma terms
  have h1 : 5 * ↑(2 * m) / 2 + 1 = ((5 * m : ℕ) + 1 : ℝ) := by
    push_cast
    ring
  have h2 : 15 * ↑(2 * m) / 2 + 1 = ((15 * m : ℕ) + 1 : ℝ) := by
    push_cast
    ring
  -- Now rewrite using Real.Gamma_nat_eq_factorial
  rw [h1, h2]
  rw [Real.Gamma_nat_eq_factorial (5 * m), Real.Gamma_nat_eq_factorial (15 * m)]
  -- Now rewrite factorials
  have h3 : 15 * (2 * m) = 30 * m := by ring
  have h4 : 2 * (2 * m) = 4 * m := by ring
  have h5 : 6 * (2 * m) = 12 * m := by ring
  have h6 : 5 * (2 * m) = 10 * m := by ring
  have h7 : 2 * m = 2 * m := by rfl
  rw [h3, h4, h5, h6, h7]


lemma a_five_val : a 5 = 3688258943632086663168 := by
  dsimp [a]
  norm_num
  have h27_2 : Gamma (27 / 2) = Gamma ((13 : ℕ) + 1 / 2) := by congr 1; norm_num
  have h77_2 : Gamma (77 / 2) = Gamma ((38 : ℕ) + 1 / 2) := by congr 1; norm_num
  rw [h27_2, h77_2]
  rw [Real.Gamma_nat_add_half 13, Real.Gamma_nat_add_half 38]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  norm_num





lemma df_5 (k : ℕ) : (10 * k + 5).doubleFactorial = (10 * k + 5) * (10 * k + 3) * (10 * k + 1).doubleFactorial := by
  have h1 : 10 * k + 5 = (10 * k + 3) + 2 := by omega
  rw [h1, doubleFactorial_add_two]
  have h2 : 10 * k + 3 = (10 * k + 1) + 2 := by omega
  rw [h2, doubleFactorial_add_two]
  ring

lemma df_15 (k : ℕ) : (30 * k + 15).doubleFactorial =
  (30 * k + 15) * (30 * k + 13) * (30 * k + 11) * (30 * k + 9) * (30 * k + 7) * (30 * k + 5) * (30 * k + 3) * (30 * k + 1).doubleFactorial := by
  have h1 : 30 * k + 15 = (30 * k + 13) + 2 := by omega
  rw [h1, doubleFactorial_add_two]
  have h2 : 30 * k + 13 = (30 * k + 11) + 2 := by omega
  rw [h2, doubleFactorial_add_two]
  have h3 : 30 * k + 11 = (30 * k + 9) + 2 := by omega
  rw [h3, doubleFactorial_add_two]
  have h4 : 30 * k + 9 = (30 * k + 7) + 2 := by omega
  rw [h4, doubleFactorial_add_two]
  have h5 : 30 * k + 7 = (30 * k + 5) + 2 := by omega
  rw [h5, doubleFactorial_add_two]
  have h6 : 30 * k + 5 = (30 * k + 3) + 2 := by omega
  rw [h6, doubleFactorial_add_two]
  have h7 : 30 * k + 3 = (30 * k + 1) + 2 := by omega
  rw [h7, doubleFactorial_add_two]
  ring

lemma a_odd (k : ℕ) : a (2 * k + 1) =
  (((15 * (2 * k + 1)).factorial : ℝ) * ((10 * k + 5).doubleFactorial : ℝ) * (2 ^ (10 * k + 5) : ℝ) * ((2 * (2 * k + 1)).factorial : ℝ)) /
  (((30 * k + 15).doubleFactorial : ℝ) * ((6 * (2 * k + 1)).factorial : ℝ) * ((5 * (2 * k + 1)).factorial : ℝ) * ((2 * k + 1).factorial : ℝ)) := by
  dsimp [a]
  have h1 : 5 * ↑(2 * k + 1) / 2 + 1 = 5 * (k : ℝ) + 3 + 1 / 2 := by
    push_cast; linarith
  have h2 : 15 * ↑(2 * k + 1) / 2 + 1 = 15 * (k : ℝ) + 8 + 1 / 2 := by
    push_cast; linarith
  rw [h1, h2]
  have h_cast1 : 5 * (k : ℝ) + 3 = ↑(5 * k + 3) := by push_cast; rfl
  have h_cast2 : 15 * (k : ℝ) + 8 = ↑(15 * k + 8) := by push_cast; rfl
  rw [h_cast1, h_cast2]
  rw [Real.Gamma_nat_add_half (5 * k + 3), Real.Gamma_nat_add_half (15 * k + 8)]
  have h3 : 2 * (5 * k + 3) - 1 = 10 * k + 5 := by omega
  have h4 : 2 * (15 * k + 8) - 1 = 30 * k + 15 := by omega
  rw [h3, h4]
  have h_df5 : ((10 * k + 5).doubleFactorial : ℝ) = ((10 * k + 5 : ℕ) : ℝ) * ((10 * k + 3 : ℕ) : ℝ) * ((10 * k + 1).doubleFactorial : ℝ) := by
    exact_mod_cast df_5 k
  have h_df15 : ((30 * k + 15).doubleFactorial : ℝ) =
    ((30 * k + 15 : ℕ) : ℝ) * ((30 * k + 13 : ℕ) : ℝ) * ((30 * k + 11 : ℕ) : ℝ) * ((30 * k + 9 : ℕ) : ℝ) *
    ((30 * k + 7 : ℕ) : ℝ) * ((30 * k + 5 : ℕ) : ℝ) * ((30 * k + 3 : ℕ) : ℝ) * ((30 * k + 1).doubleFactorial : ℝ) := by
    exact_mod_cast df_15 k
  rw [h_df5, h_df15]
  have h_pow : (2 : ℝ) ^ (15 * k + 8) = 2 ^ (10 * k + 5) * 2 ^ (5 * k + 3) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h_pow]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  push_cast
  ring

