import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

/--
A080326: Denominator of $\sum_{k=1}^n k^{\mu(k)}$, where $\mu$ is the Moebius function (A008683).
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

theorem a_1 : a 1 = primorial 1 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  simp
  decide

theorem a_2 : a 2 = primorial 2 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  rw [h2]
  norm_num
  decide

theorem a_3 : a 3 = primorial 3 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3]
  norm_num
  decide

theorem a_4 : a 4 = primorial 4 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  rw [h2, h3, h4]
  norm_num
  decide

theorem a_5 : a 5 = primorial 5 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5]
  norm_num
  decide

theorem a_6 : a 6 = primorial 6 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  rw [h2, h3, h4, h5, h6]
  norm_num
  decide

theorem a_7 : a 7 = primorial 7 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5, h6, h7]
  norm_num
  decide

theorem a_8 : a 8 = primorial 8 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  rw [h2, h3, h4, h5, h6, h7, h8]
  norm_num
  decide

theorem a_9 : a 9 = primorial 9 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  rw [h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  decide

theorem a_10 : a 10 = primorial 10 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h10_eq : 10 = 2 * 5 := by decide
    rw [h10_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [h2, h5]; decide
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num
  decide

theorem a_11 : a 11 = primorial 11 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h6_eq : 6 = 2 * 3 := by decide
    rw [h6_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [h2, h3]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h10_eq : 10 = 2 * 5 := by decide
    rw [h10_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
    have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [h2, h5]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  norm_num
  decide

theorem a_12 : a 12 = primorial 12 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  norm_num
  decide

theorem a_13 : a 13 = primorial 13 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  norm_num
  decide

theorem a_14 : a 14 = primorial 14 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  norm_num
  decide

theorem a_15 : a 15 = primorial 15 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  norm_num
  decide

theorem a_16 : a 16 = primorial 16 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  norm_num
  decide

theorem a_17 : a 17 = primorial 17 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h17 : moebius 17 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  norm_num
  decide

theorem a_18 : a 18 = primorial 18 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h17 : moebius 17 = -1 := moebius_apply_prime (by decide)
  have h18 : moebius 18 = 0 := by
    have hcop : Coprime (3 ^ 2) 2 := by decide
    have h_eq : 18 = (3 ^ 2) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
  norm_num
  decide

theorem a_19 : a 19 = primorial 19 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h17 : moebius 17 = -1 := moebius_apply_prime (by decide)
  have h18 : moebius 18 = 0 := by
    have hcop : Coprime (3 ^ 2) 2 := by decide
    have h_eq : 18 = (3 ^ 2) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h19 : moebius 19 = -1 := moebius_apply_prime (by decide)
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  norm_num
  decide

theorem a_20 : a 20 = primorial 20 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 7 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    have hq : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, hq]; decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]
    rfl
  have h17 : moebius 17 = -1 := moebius_apply_prime (by decide)
  have h18 : moebius 18 = 0 := by
    have hcop : Coprime (3 ^ 2) 2 := by decide
    have h_eq : 18 = (3 ^ 2) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  have h19 : moebius 19 = -1 := moebius_apply_prime (by decide)
  have h20 : moebius 20 = 0 := by
    have hcop : Coprime (2 ^ 2) 5 := by decide
    have h_eq : 20 = (2 ^ 2) * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]
      rfl
    rw [hpow, zero_mul]
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  norm_num
  decide


theorem a_70 : a 70 = primorial 70 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := moebius_apply_prime (by decide)
  have h4 : moebius 4 = 0 := by
    have h4_eq : 4 = 2 ^ 2 := by decide
    rw [h4_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h5 : moebius 5 = -1 := moebius_apply_prime (by decide)
  have h6 : moebius 6 = 1 := by
    have hcop : Coprime 2 3 := by decide
    have h_eq : 6 = 2 * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h3]
    decide
  have h7 : moebius 7 = -1 := moebius_apply_prime (by decide)
  have h8 : moebius 8 = 0 := by
    have h8_eq : 8 = 2 ^ 3 := by decide
    rw [h8_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h9 : moebius 9 = 0 := by
    have h9_eq : 9 = 3 ^ 2 := by decide
    rw [h9_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h10 : moebius 10 = 1 := by
    have hcop : Coprime 2 5 := by decide
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h5]
    decide
  have h11 : moebius 11 = -1 := moebius_apply_prime (by decide)
  have h12 : moebius 12 = 0 := by
    have hcop : Coprime (2 ^ 2) 3 := by decide
    have h_eq : 12 = (2 ^ 2) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h13 : moebius 13 = -1 := moebius_apply_prime (by decide)
  have h14 : moebius 14 = 1 := by
    have hcop : Coprime 2 7 := by decide
    have h_eq : 14 = 2 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h7]
    decide
  have h15 : moebius 15 = 1 := by
    have hcop : Coprime 3 5 := by decide
    have h_eq : 15 = 3 * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h5]
    decide
  have h16 : moebius 16 = 0 := by
    have h16_eq : 16 = 2 ^ 4 := by decide
    rw [h16_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h17 : moebius 17 = -1 := moebius_apply_prime (by decide)
  have h18 : moebius 18 = 0 := by
    have hcop : Coprime (3 ^ 2) 2 := by decide
    have h_eq : 18 = (3 ^ 2) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h19 : moebius 19 = -1 := moebius_apply_prime (by decide)
  have h20 : moebius 20 = 0 := by
    have hcop : Coprime (2 ^ 2) 5 := by decide
    have h_eq : 20 = (2 ^ 2) * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h21 : moebius 21 = 1 := by
    have hcop : Coprime 3 7 := by decide
    have h_eq : 21 = 3 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h7]
    decide
  have h22 : moebius 22 = 1 := by
    have hcop : Coprime 2 11 := by decide
    have h_eq : 22 = 2 * 11 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h11]
    decide
  have h23 : moebius 23 = -1 := moebius_apply_prime (by decide)
  have h24 : moebius 24 = 0 := by
    have hcop : Coprime (2 ^ 3) 3 := by decide
    have h_eq : 24 = (2 ^ 3) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 3) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h25 : moebius 25 = 0 := by
    have h25_eq : 25 = 5 ^ 2 := by decide
    rw [h25_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h26 : moebius 26 = 1 := by
    have hcop : Coprime 2 13 := by decide
    have h_eq : 26 = 2 * 13 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h13]
    decide
  have h27 : moebius 27 = 0 := by
    have h27_eq : 27 = 3 ^ 3 := by decide
    rw [h27_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h28 : moebius 28 = 0 := by
    have hcop : Coprime (2 ^ 2) 7 := by decide
    have h_eq : 28 = (2 ^ 2) * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h29 : moebius 29 = -1 := moebius_apply_prime (by decide)
  have h30 : moebius 30 = -1 := by
    have hcop : Coprime 2 15 := by decide
    have h_eq : 30 = 2 * 15 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h15]
    decide
  have h31 : moebius 31 = -1 := moebius_apply_prime (by decide)
  have h32 : moebius 32 = 0 := by
    have h32_eq : 32 = 2 ^ 5 := by decide
    rw [h32_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h33 : moebius 33 = 1 := by
    have hcop : Coprime 3 11 := by decide
    have h_eq : 33 = 3 * 11 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h11]
    decide
  have h34 : moebius 34 = 1 := by
    have hcop : Coprime 2 17 := by decide
    have h_eq : 34 = 2 * 17 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h17]
    decide
  have h35 : moebius 35 = 1 := by
    have hcop : Coprime 5 7 := by decide
    have h_eq : 35 = 5 * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, h7]
    decide
  have h36 : moebius 36 = 0 := by
    have hcop : Coprime (2 ^ 2) 9 := by decide
    have h_eq : 36 = (2 ^ 2) * 9 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h37 : moebius 37 = -1 := moebius_apply_prime (by decide)
  have h38 : moebius 38 = 1 := by
    have hcop : Coprime 2 19 := by decide
    have h_eq : 38 = 2 * 19 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h19]
    decide
  have h39 : moebius 39 = 1 := by
    have hcop : Coprime 3 13 := by decide
    have h_eq : 39 = 3 * 13 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h13]
    decide
  have h40 : moebius 40 = 0 := by
    have hcop : Coprime (2 ^ 3) 5 := by decide
    have h_eq : 40 = (2 ^ 3) * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 3) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h41 : moebius 41 = -1 := moebius_apply_prime (by decide)
  have h42 : moebius 42 = -1 := by
    have hcop : Coprime 2 21 := by decide
    have h_eq : 42 = 2 * 21 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h21]
    decide
  have h43 : moebius 43 = -1 := moebius_apply_prime (by decide)
  have h44 : moebius 44 = 0 := by
    have hcop : Coprime (2 ^ 2) 11 := by decide
    have h_eq : 44 = (2 ^ 2) * 11 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h45 : moebius 45 = 0 := by
    have hcop : Coprime (3 ^ 2) 5 := by decide
    have h_eq : 45 = (3 ^ 2) * 5 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h46 : moebius 46 = 1 := by
    have hcop : Coprime 2 23 := by decide
    have h_eq : 46 = 2 * 23 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h23]
    decide
  have h47 : moebius 47 = -1 := moebius_apply_prime (by decide)
  have h48 : moebius 48 = 0 := by
    have hcop : Coprime (2 ^ 4) 3 := by decide
    have h_eq : 48 = (2 ^ 4) * 3 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 4) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h49 : moebius 49 = 0 := by
    have h49_eq : 49 = 7 ^ 2 := by decide
    rw [h49_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h50 : moebius 50 = 0 := by
    have hcop : Coprime (5 ^ 2) 2 := by decide
    have h_eq : 50 = (5 ^ 2) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (5 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h51 : moebius 51 = 1 := by
    have hcop : Coprime 3 17 := by decide
    have h_eq : 51 = 3 * 17 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h17]
    decide
  have h52 : moebius 52 = 0 := by
    have hcop : Coprime (2 ^ 2) 13 := by decide
    have h_eq : 52 = (2 ^ 2) * 13 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h53 : moebius 53 = -1 := moebius_apply_prime (by decide)
  have h54 : moebius 54 = 0 := by
    have hcop : Coprime (3 ^ 3) 2 := by decide
    have h_eq : 54 = (3 ^ 3) * 2 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 3) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h55 : moebius 55 = 1 := by
    have hcop : Coprime 5 11 := by decide
    have h_eq : 55 = 5 * 11 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, h11]
    decide
  have h56 : moebius 56 = 0 := by
    have hcop : Coprime (2 ^ 3) 7 := by decide
    have h_eq : 56 = (2 ^ 3) * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 3) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h57 : moebius 57 = 1 := by
    have hcop : Coprime 3 19 := by decide
    have h_eq : 57 = 3 * 19 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h19]
    decide
  have h58 : moebius 58 = 1 := by
    have hcop : Coprime 2 29 := by decide
    have h_eq : 58 = 2 * 29 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h29]
    decide
  have h59 : moebius 59 = -1 := moebius_apply_prime (by decide)
  have h60 : moebius 60 = 0 := by
    have hcop : Coprime (2 ^ 2) 15 := by decide
    have h_eq : 60 = (2 ^ 2) * 15 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h61 : moebius 61 = -1 := moebius_apply_prime (by decide)
  have h62 : moebius 62 = 1 := by
    have hcop : Coprime 2 31 := by decide
    have h_eq : 62 = 2 * 31 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h31]
    decide
  have h63 : moebius 63 = 0 := by
    have hcop : Coprime (3 ^ 2) 7 := by decide
    have h_eq : 63 = (3 ^ 2) * 7 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (3 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h64 : moebius 64 = 0 := by
    have h64_eq : 64 = 2 ^ 6 := by decide
    rw [h64_eq, moebius_apply_prime_pow (by decide) (by decide)]; rfl
  have h65 : moebius 65 = 1 := by
    have hcop : Coprime 5 13 := by decide
    have h_eq : 65 = 5 * 13 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 5 = -1 := moebius_apply_prime (by decide)
    rw [hp, h13]
    decide
  have h66 : moebius 66 = -1 := by
    have hcop : Coprime 2 33 := by decide
    have h_eq : 66 = 2 * 33 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h33]
    decide
  have h67 : moebius 67 = -1 := moebius_apply_prime (by decide)
  have h68 : moebius 68 = 0 := by
    have hcop : Coprime (2 ^ 2) 17 := by decide
    have h_eq : 68 = (2 ^ 2) * 17 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hpow : moebius (2 ^ 2) = 0 := by
      rw [moebius_apply_prime_pow (by decide) (by decide)]; rfl
    rw [hpow, zero_mul]
  have h69 : moebius 69 = 1 := by
    have hcop : Coprime 3 23 := by decide
    have h_eq : 69 = 3 * 23 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 3 = -1 := moebius_apply_prime (by decide)
    rw [hp, h23]
    decide
  have h70 : moebius 70 = -1 := by
    have hcop : Coprime 2 35 := by decide
    have h_eq : 70 = 2 * 35 := by decide
    rw [h_eq, isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hp : moebius 2 = -1 := moebius_apply_prime (by decide)
    rw [hp, h35]
    decide
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70]
  norm_num
  decide

/--
Does a(n) = A034386(n) for infinitely many n?
Conjecture: The set of $n$ such that $a(n)$ equals the primorial of $n$ is infinite.
A034386(n) is `Nat.primorial n`.
-/
theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := by
  sorry
