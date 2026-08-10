import FormalConjectures.Util.ProblemImports
open ArithmeticFunction Finset Nat
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den
theorem a_1 : a 1 = primorial 1 := by
  unfold a; unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  simp
  norm_num
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
  decide#print axioms a_11
