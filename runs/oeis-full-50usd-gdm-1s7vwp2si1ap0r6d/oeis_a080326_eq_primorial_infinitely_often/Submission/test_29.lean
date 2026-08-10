import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

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

