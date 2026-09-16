import FormalConjectures.Util.ProblemImports

lemma p2_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 2) ≠ 0 := by
  have hk : 2 ^ (10 * n + 2) + 2 = 2 + 2 ^ (10 * n + 2) := by omega
  calc
    (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 2) = 2 ^ (2 + 2 ^ (10 * n + 2)) + 3 := by rw [hk]
    _ = 2 ^ 2 * 2 ^ (2 ^ (10 * n + 2)) + 3 := by rw [pow_add]
    _ = 0 * (2 ^ (2 ^ (10 * n + 2)) : ZMod 2) + 1 := by
      have h1 : (2 ^ 2 : ZMod 2) = 0 := by decide
      have h2 : (3 : ZMod 2) = 1 := by decide
      rw [h1, h2]
    _ = 1 := by ring
    _ ≠ 0 := by decide

lemma p3_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 2 * m + 0 := by
  induction' k with k ih
  · use 2; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 0
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (2 * m + 0) * 2 ^ 10 := by rw [hm]
      _ = 2 * (m * 1024 + 0) + 0 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p3_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 3) ≠ 0 := by
  have ⟨m, hm⟩ := p3_exp_0 k
  have hexp2 : 2 * m + 0 + 2 = 2 * m + 2 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 3) = 2 ^ (2 * m + 0 + 2) + 3 := by rw [hm]
    _ = 2 ^ (2 * m + 2) + 3 := by rw [hexp2]
    _ = 2 ^ (2 * m) * 2 ^ 2 + 3 := by rw [pow_add]
    _ = (2 ^ 2) ^ m * 2 ^ 2 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 2 + 3 := by
      have h1 : (2 ^ 2 : ZMod 3) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 2 + 3 := by rw [one_pow]
    _ = 2 ^ 2 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p3_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 3) ≠ 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p3_not_dvd_0 n

lemma p5_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 4 * m + 0 := by
  induction' k with k ih
  · use 1; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 0
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (4 * m + 0) * 2 ^ 10 := by rw [hm]
      _ = 4 * (m * 1024 + 0) + 0 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p5_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 5) ≠ 0 := by
  have ⟨m, hm⟩ := p5_exp_0 k
  have hexp2 : 4 * m + 0 + 2 = 4 * m + 2 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 5) = 2 ^ (4 * m + 0 + 2) + 3 := by rw [hm]
    _ = 2 ^ (4 * m + 2) + 3 := by rw [hexp2]
    _ = 2 ^ (4 * m) * 2 ^ 2 + 3 := by rw [pow_add]
    _ = (2 ^ 4) ^ m * 2 ^ 2 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 2 + 3 := by
      have h1 : (2 ^ 4 : ZMod 5) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 2 + 3 := by rw [one_pow]
    _ = 2 ^ 2 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p5_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 5) ≠ 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p5_not_dvd_0 n

lemma p7_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 6 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 682
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (6 * m + 4) * 2 ^ 10 := by rw [hm]
      _ = 6 * (m * 1024 + 682) + 4 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p7_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 7) ≠ 0 := by
  have ⟨m, hm⟩ := p7_exp_0 k
  have hexp2 : 6 * m + 4 + 2 = 6 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 7) = 2 ^ (6 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (6 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (6 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 6) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 6 : ZMod 7) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p7_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 7) ≠ 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p7_not_dvd_0 n

lemma p11_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 0) + 2) = 10 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 419430
    have hexp : 10 * (2 * (k + 1) + 0) + 2 = 10 * (2 * k + 0) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 0) + 2) = 2 ^ (10 * (2 * k + 0) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 0) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (10 * m + 4) * 2 ^ 20 := by rw [hm]
      _ = 10 * (m * 1048576 + 419430) + 4 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p11_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 11) ≠ 0 := by
  have ⟨m, hm⟩ := p11_exp_0 k
  have hexp2 : 10 * m + 4 + 2 = 10 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 11) = 2 ^ (10 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (10 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (10 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 10) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 10 : ZMod 11) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p11_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 1) + 2) = 10 * m + 6 := by
  induction' k with k ih
  · use 409; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 629145
    have hexp : 10 * (2 * (k + 1) + 1) + 2 = 10 * (2 * k + 1) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 1) + 2) = 2 ^ (10 * (2 * k + 1) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 1) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (10 * m + 6) * 2 ^ 20 := by rw [hm]
      _ = 10 * (m * 1048576 + 629145) + 6 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p11_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 11) ≠ 0 := by
  have ⟨m, hm⟩ := p11_exp_1 k
  have hexp2 : 10 * m + 6 + 2 = 10 * m + 8 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 11) = 2 ^ (10 * m + 6 + 2) + 3 := by rw [hm]
    _ = 2 ^ (10 * m + 8) + 3 := by rw [hexp2]
    _ = 2 ^ (10 * m) * 2 ^ 8 + 3 := by rw [pow_add]
    _ = (2 ^ 10) ^ m * 2 ^ 8 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 8 + 3 := by
      have h1 : (2 ^ 10 : ZMod 11) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 8 + 3 := by rw [one_pow]
    _ = 2 ^ 8 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p11_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 11) ≠ 0 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · have h_eq : n = 2 * (n / 2) + 0 := by omega
    rw [h_eq]
    exact p11_not_dvd_0 (n / 2)
  · have h_eq : n = 2 * (n / 2) + 1 := by omega
    rw [h_eq]
    exact p11_not_dvd_1 (n / 2)

lemma p13_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 12 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 341
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (12 * m + 4) * 2 ^ 10 := by rw [hm]
      _ = 12 * (m * 1024 + 341) + 4 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p13_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 13) ≠ 0 := by
  have ⟨m, hm⟩ := p13_exp_0 k
  have hexp2 : 12 * m + 4 + 2 = 12 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 13) = 2 ^ (12 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (12 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (12 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 12) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 12 : ZMod 13) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p13_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 13) ≠ 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p13_not_dvd_0 n

lemma p17_pre_0 : (2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 : ZMod 17) ≠ 0 := by decide

lemma p17_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 1) + 2) = 16 * m + 0 := by
  induction' k with k ih
  · use 256; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 0
    have hexp : 10 * (1 * (k + 1) + 1) + 2 = 10 * (1 * k + 1) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 1) + 2) = 2 ^ (10 * (1 * k + 1) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 1) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (16 * m + 0) * 2 ^ 10 := by rw [hm]
      _ = 16 * (m * 1024 + 0) + 0 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p17_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 1) + 2) + 2) + 3 : ZMod 17) ≠ 0 := by
  have ⟨m, hm⟩ := p17_exp_0 k
  have hexp2 : 16 * m + 0 + 2 = 16 * m + 2 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 1) + 2) + 2) + 3 : ZMod 17) = 2 ^ (16 * m + 0 + 2) + 3 := by rw [hm]
    _ = 2 ^ (16 * m + 2) + 3 := by rw [hexp2]
    _ = 2 ^ (16 * m) * 2 ^ 2 + 3 := by rw [pow_add]
    _ = (2 ^ 16) ^ m * 2 ^ 2 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 2 + 3 := by
      have h1 : (2 ^ 16 : ZMod 17) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 2 + 3 := by rw [one_pow]
    _ = 2 ^ 2 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p17_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 17) ≠ 0 := by
  have h_pre : n < 1 ∨ 1 ≤ n := by omega
  rcases h_pre with h_lt | h_ge
  · have h0 : n = 0 := by omega
    rw [h0]
    exact p17_pre_0
  · have h_eq : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
    rcases h_eq with ⟨m, hm_eq⟩
    have h_eq2 : n = 1 * m + 1 := by omega
    rw [h_eq2]
    exact p17_not_dvd_0 m

lemma p19_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 0) + 2) = 18 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 238609294
    have hexp : 10 * (3 * (k + 1) + 0) + 2 = 10 * (3 * k + 0) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 0) + 2) = 2 ^ (10 * (3 * k + 0) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 0) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (18 * m + 4) * 2 ^ 30 := by rw [hm]
      _ = 18 * (m * 1073741824 + 238609294) + 4 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p19_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 19) ≠ 0 := by
  have ⟨m, hm⟩ := p19_exp_0 k
  have hexp2 : 18 * m + 4 + 2 = 18 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 19) = 2 ^ (18 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (18 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (18 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 18) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 18 : ZMod 19) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p19_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 1) + 2) = 18 * m + 10 := by
  induction' k with k ih
  · use 227; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 596523235
    have hexp : 10 * (3 * (k + 1) + 1) + 2 = 10 * (3 * k + 1) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 1) + 2) = 2 ^ (10 * (3 * k + 1) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 1) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (18 * m + 10) * 2 ^ 30 := by rw [hm]
      _ = 18 * (m * 1073741824 + 596523235) + 10 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p19_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 19) ≠ 0 := by
  have ⟨m, hm⟩ := p19_exp_1 k
  have hexp2 : 18 * m + 10 + 2 = 18 * m + 12 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 19) = 2 ^ (18 * m + 10 + 2) + 3 := by rw [hm]
    _ = 2 ^ (18 * m + 12) + 3 := by rw [hexp2]
    _ = 2 ^ (18 * m) * 2 ^ 12 + 3 := by rw [pow_add]
    _ = (2 ^ 18) ^ m * 2 ^ 12 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 12 + 3 := by
      have h1 : (2 ^ 18 : ZMod 19) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 12 + 3 := by rw [one_pow]
    _ = 2 ^ 12 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p19_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 2) + 2) = 18 * m + 16 := by
  induction' k with k ih
  · use 233016; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 954437176
    have hexp : 10 * (3 * (k + 1) + 2) + 2 = 10 * (3 * k + 2) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 2) + 2) = 2 ^ (10 * (3 * k + 2) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 2) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (18 * m + 16) * 2 ^ 30 := by rw [hm]
      _ = 18 * (m * 1073741824 + 954437176) + 16 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p19_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 19) ≠ 0 := by
  have ⟨m, hm⟩ := p19_exp_2 k
  have hexp2 : 18 * m + 16 + 2 = 18 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 19) = 2 ^ (18 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (18 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (18 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 18) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 18 : ZMod 19) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p19_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 19) ≠ 0 := by
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · have h_eq : n = 3 * (n / 3) + 0 := by omega
    rw [h_eq]
    exact p19_not_dvd_0 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 1 := by omega
    rw [h_eq]
    exact p19_not_dvd_1 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 2 := by omega
    rw [h_eq]
    exact p19_not_dvd_2 (n / 3)

lemma p23_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 22 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 186
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (22 * m + 4) * 2 ^ 10 := by rw [hm]
      _ = 22 * (m * 1024 + 186) + 4 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p23_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 23) ≠ 0 := by
  have ⟨m, hm⟩ := p23_exp_0 k
  have hexp2 : 22 * m + 4 + 2 = 22 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 23) = 2 ^ (22 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (22 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (22 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 22) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 22 : ZMod 23) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p23_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 23) ≠ 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p23_not_dvd_0 n

lemma p29_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 0) + 2) = 28 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 153391689
    have hexp : 10 * (3 * (k + 1) + 0) + 2 = 10 * (3 * k + 0) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 0) + 2) = 2 ^ (10 * (3 * k + 0) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 0) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (28 * m + 4) * 2 ^ 30 := by rw [hm]
      _ = 28 * (m * 1073741824 + 153391689) + 4 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p29_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 29) ≠ 0 := by
  have ⟨m, hm⟩ := p29_exp_0 k
  have hexp2 : 28 * m + 4 + 2 = 28 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 29) = 2 ^ (28 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (28 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (28 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 28) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 28 : ZMod 29) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p29_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 1) + 2) = 28 * m + 8 := by
  induction' k with k ih
  · use 146; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 306783378
    have hexp : 10 * (3 * (k + 1) + 1) + 2 = 10 * (3 * k + 1) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 1) + 2) = 2 ^ (10 * (3 * k + 1) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 1) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (28 * m + 8) * 2 ^ 30 := by rw [hm]
      _ = 28 * (m * 1073741824 + 306783378) + 8 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p29_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 29) ≠ 0 := by
  have ⟨m, hm⟩ := p29_exp_1 k
  have hexp2 : 28 * m + 8 + 2 = 28 * m + 10 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 29) = 2 ^ (28 * m + 8 + 2) + 3 := by rw [hm]
    _ = 2 ^ (28 * m + 10) + 3 := by rw [hexp2]
    _ = 2 ^ (28 * m) * 2 ^ 10 + 3 := by rw [pow_add]
    _ = (2 ^ 28) ^ m * 2 ^ 10 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 10 + 3 := by
      have h1 : (2 ^ 28 : ZMod 29) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 10 + 3 := by rw [one_pow]
    _ = 2 ^ 10 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p29_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 2) + 2) = 28 * m + 16 := by
  induction' k with k ih
  · use 149796; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 613566756
    have hexp : 10 * (3 * (k + 1) + 2) + 2 = 10 * (3 * k + 2) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 2) + 2) = 2 ^ (10 * (3 * k + 2) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 2) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (28 * m + 16) * 2 ^ 30 := by rw [hm]
      _ = 28 * (m * 1073741824 + 613566756) + 16 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p29_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 29) ≠ 0 := by
  have ⟨m, hm⟩ := p29_exp_2 k
  have hexp2 : 28 * m + 16 + 2 = 28 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 29) = 2 ^ (28 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (28 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (28 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 28) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 28 : ZMod 29) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p29_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 29) ≠ 0 := by
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · have h_eq : n = 3 * (n / 3) + 0 := by omega
    rw [h_eq]
    exact p29_not_dvd_0 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 1 := by omega
    rw [h_eq]
    exact p29_not_dvd_1 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 2 := by omega
    rw [h_eq]
    exact p29_not_dvd_2 (n / 3)

lemma p31_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 0) + 2) = 30 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 139810
    have hexp : 10 * (2 * (k + 1) + 0) + 2 = 10 * (2 * k + 0) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 0) + 2) = 2 ^ (10 * (2 * k + 0) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 0) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (30 * m + 4) * 2 ^ 20 := by rw [hm]
      _ = 30 * (m * 1048576 + 139810) + 4 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p31_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 31) ≠ 0 := by
  have ⟨m, hm⟩ := p31_exp_0 k
  have hexp2 : 30 * m + 4 + 2 = 30 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 31) = 2 ^ (30 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (30 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (30 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 30) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 30 : ZMod 31) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p31_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 1) + 2) = 30 * m + 16 := by
  induction' k with k ih
  · use 136; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 559240
    have hexp : 10 * (2 * (k + 1) + 1) + 2 = 10 * (2 * k + 1) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 1) + 2) = 2 ^ (10 * (2 * k + 1) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 1) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (30 * m + 16) * 2 ^ 20 := by rw [hm]
      _ = 30 * (m * 1048576 + 559240) + 16 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p31_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 31) ≠ 0 := by
  have ⟨m, hm⟩ := p31_exp_1 k
  have hexp2 : 30 * m + 16 + 2 = 30 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 31) = 2 ^ (30 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (30 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (30 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 30) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 30 : ZMod 31) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p31_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 31) ≠ 0 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · have h_eq : n = 2 * (n / 2) + 0 := by omega
    rw [h_eq]
    exact p31_not_dvd_0 (n / 2)
  · have h_eq : n = 2 * (n / 2) + 1 := by omega
    rw [h_eq]
    exact p31_not_dvd_1 (n / 2)

lemma p37_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 0) + 2) = 36 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 119304647
    have hexp : 10 * (3 * (k + 1) + 0) + 2 = 10 * (3 * k + 0) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 0) + 2) = 2 ^ (10 * (3 * k + 0) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 0) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (36 * m + 4) * 2 ^ 30 := by rw [hm]
      _ = 36 * (m * 1073741824 + 119304647) + 4 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p37_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 37) ≠ 0 := by
  have ⟨m, hm⟩ := p37_exp_0 k
  have hexp2 : 36 * m + 4 + 2 = 36 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 37) = 2 ^ (36 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (36 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (36 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 36) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 36 : ZMod 37) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p37_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 1) + 2) = 36 * m + 28 := by
  induction' k with k ih
  · use 113; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 835132529
    have hexp : 10 * (3 * (k + 1) + 1) + 2 = 10 * (3 * k + 1) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 1) + 2) = 2 ^ (10 * (3 * k + 1) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 1) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (36 * m + 28) * 2 ^ 30 := by rw [hm]
      _ = 36 * (m * 1073741824 + 835132529) + 28 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p37_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 37) ≠ 0 := by
  have ⟨m, hm⟩ := p37_exp_1 k
  have hexp2 : 36 * m + 28 + 2 = 36 * m + 30 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 37) = 2 ^ (36 * m + 28 + 2) + 3 := by rw [hm]
    _ = 2 ^ (36 * m + 30) + 3 := by rw [hexp2]
    _ = 2 ^ (36 * m) * 2 ^ 30 + 3 := by rw [pow_add]
    _ = (2 ^ 36) ^ m * 2 ^ 30 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 30 + 3 := by
      have h1 : (2 ^ 36 : ZMod 37) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 30 + 3 := by rw [one_pow]
    _ = 2 ^ 30 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p37_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 2) + 2) = 36 * m + 16 := by
  induction' k with k ih
  · use 116508; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 477218588
    have hexp : 10 * (3 * (k + 1) + 2) + 2 = 10 * (3 * k + 2) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 2) + 2) = 2 ^ (10 * (3 * k + 2) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 2) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (36 * m + 16) * 2 ^ 30 := by rw [hm]
      _ = 36 * (m * 1073741824 + 477218588) + 16 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p37_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 37) ≠ 0 := by
  have ⟨m, hm⟩ := p37_exp_2 k
  have hexp2 : 36 * m + 16 + 2 = 36 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 37) = 2 ^ (36 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (36 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (36 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 36) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 36 : ZMod 37) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p37_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 37) ≠ 0 := by
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · have h_eq : n = 3 * (n / 3) + 0 := by omega
    rw [h_eq]
    exact p37_not_dvd_0 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 1 := by omega
    rw [h_eq]
    exact p37_not_dvd_1 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 2 := by omega
    rw [h_eq]
    exact p37_not_dvd_2 (n / 3)

lemma p41_pre_0 : (2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 : ZMod 41) ≠ 0 := by decide

lemma p41_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 1) + 2) = 40 * m + 16 := by
  induction' k with k ih
  · use 102; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 419430
    have hexp : 10 * (2 * (k + 1) + 1) + 2 = 10 * (2 * k + 1) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 1) + 2) = 2 ^ (10 * (2 * k + 1) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 1) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (40 * m + 16) * 2 ^ 20 := by rw [hm]
      _ = 40 * (m * 1048576 + 419430) + 16 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p41_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 41) ≠ 0 := by
  have ⟨m, hm⟩ := p41_exp_0 k
  have hexp2 : 40 * m + 16 + 2 = 40 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 41) = 2 ^ (40 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (40 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (40 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 40) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 40 : ZMod 41) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p41_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 2) + 2) = 40 * m + 24 := by
  induction' k with k ih
  · use 104857; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 629145
    have hexp : 10 * (2 * (k + 1) + 2) + 2 = 10 * (2 * k + 2) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 2) + 2) = 2 ^ (10 * (2 * k + 2) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 2) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (40 * m + 24) * 2 ^ 20 := by rw [hm]
      _ = 40 * (m * 1048576 + 629145) + 24 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p41_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 2) + 2) + 2) + 3 : ZMod 41) ≠ 0 := by
  have ⟨m, hm⟩ := p41_exp_1 k
  have hexp2 : 40 * m + 24 + 2 = 40 * m + 26 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 2) + 2) + 2) + 3 : ZMod 41) = 2 ^ (40 * m + 24 + 2) + 3 := by rw [hm]
    _ = 2 ^ (40 * m + 26) + 3 := by rw [hexp2]
    _ = 2 ^ (40 * m) * 2 ^ 26 + 3 := by rw [pow_add]
    _ = (2 ^ 40) ^ m * 2 ^ 26 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 26 + 3 := by
      have h1 : (2 ^ 40 : ZMod 41) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 26 + 3 := by rw [one_pow]
    _ = 2 ^ 26 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p41_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 41) ≠ 0 := by
  have h_pre : n < 1 ∨ 1 ≤ n := by omega
  rcases h_pre with h_lt | h_ge
  · have h0 : n = 0 := by omega
    rw [h0]
    exact p41_pre_0
  · have h_eq : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
    rcases h_eq with ⟨m, hm_eq⟩
    have h_cases : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h_cases with h0 | h1
    · have h_eq2 : n = 2 * (m / 2) + 1 := by omega
      rw [h_eq2]
      exact p41_not_dvd_0 (m / 2)

    · have h_eq2 : n = 2 * (m / 2) + 2 := by omega
      rw [h_eq2]
      exact p41_not_dvd_1 (m / 2)

lemma p43_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 0) + 2) = 42 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 102261126
    have hexp : 10 * (3 * (k + 1) + 0) + 2 = 10 * (3 * k + 0) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 0) + 2) = 2 ^ (10 * (3 * k + 0) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 0) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (42 * m + 4) * 2 ^ 30 := by rw [hm]
      _ = 42 * (m * 1073741824 + 102261126) + 4 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p43_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 43) ≠ 0 := by
  have ⟨m, hm⟩ := p43_exp_0 k
  have hexp2 : 42 * m + 4 + 2 = 42 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 0) + 2) + 2) + 3 : ZMod 43) = 2 ^ (42 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (42 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (42 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 42) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 42 : ZMod 43) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p43_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 1) + 2) = 42 * m + 22 := by
  induction' k with k ih
  · use 97; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 562436193
    have hexp : 10 * (3 * (k + 1) + 1) + 2 = 10 * (3 * k + 1) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 1) + 2) = 2 ^ (10 * (3 * k + 1) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 1) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (42 * m + 22) * 2 ^ 30 := by rw [hm]
      _ = 42 * (m * 1073741824 + 562436193) + 22 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p43_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 43) ≠ 0 := by
  have ⟨m, hm⟩ := p43_exp_1 k
  have hexp2 : 42 * m + 22 + 2 = 42 * m + 24 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 1) + 2) + 2) + 3 : ZMod 43) = 2 ^ (42 * m + 22 + 2) + 3 := by rw [hm]
    _ = 2 ^ (42 * m + 24) + 3 := by rw [hexp2]
    _ = 2 ^ (42 * m) * 2 ^ 24 + 3 := by rw [pow_add]
    _ = (2 ^ 42) ^ m * 2 ^ 24 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 24 + 3 := by
      have h1 : (2 ^ 42 : ZMod 43) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 24 + 3 := by rw [one_pow]
    _ = 2 ^ 24 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p43_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (3 * k + 2) + 2) = 42 * m + 16 := by
  induction' k with k ih
  · use 99864; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1073741824 + 409044504
    have hexp : 10 * (3 * (k + 1) + 2) + 2 = 10 * (3 * k + 2) + 2 + 30 := by omega
    calc
      2 ^ (10 * (3 * (k + 1) + 2) + 2) = 2 ^ (10 * (3 * k + 2) + 2 + 30) := by rw [hexp]
      _ = 2 ^ (10 * (3 * k + 2) + 2) * 2 ^ 30 := by rw [pow_add]
      _ = (42 * m + 16) * 2 ^ 30 := by rw [hm]
      _ = 42 * (m * 1073741824 + 409044504) + 16 := by
        have h_mult : 2 ^ 30 = 1073741824 := by decide
        rw [h_mult]
        omega

lemma p43_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 43) ≠ 0 := by
  have ⟨m, hm⟩ := p43_exp_2 k
  have hexp2 : 42 * m + 16 + 2 = 42 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (3 * k + 2) + 2) + 2) + 3 : ZMod 43) = 2 ^ (42 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (42 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (42 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 42) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 42 : ZMod 43) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p43_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 43) ≠ 0 := by
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · have h_eq : n = 3 * (n / 3) + 0 := by omega
    rw [h_eq]
    exact p43_not_dvd_0 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 1 := by omega
    rw [h_eq]
    exact p43_not_dvd_1 (n / 3)
  · have h_eq : n = 3 * (n / 3) + 2 := by omega
    rw [h_eq]
    exact p43_not_dvd_2 (n / 3)

lemma p47_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 0) + 2) = 46 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 112876018663800600620228181070002
    have hexp : 10 * (11 * (k + 1) + 0) + 2 = 10 * (11 * k + 0) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 0) + 2) = 2 ^ (10 * (11 * k + 0) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 0) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 4) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 112876018663800600620228181070002) + 4 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 0) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_0 k
  have hexp2 : 46 * m + 4 + 2 = 46 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 0) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 1) + 2) = 46 * m + 2 := by
  induction' k with k ih
  · use 89; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 56438009331900300310114090535001
    have hexp : 10 * (11 * (k + 1) + 1) + 2 = 10 * (11 * k + 1) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 1) + 2) = 2 ^ (10 * (11 * k + 1) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 1) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 2) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 56438009331900300310114090535001) + 2 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 1) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_1 k
  have hexp2 : 46 * m + 2 + 2 = 46 * m + 4 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 1) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 2 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 4) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 4 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 4 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 4 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 4 + 3 := by rw [one_pow]
    _ = 2 ^ 4 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 2) + 2) = 46 * m + 24 := by
  induction' k with k ih
  · use 91180; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 677256111982803603721369086420012
    have hexp : 10 * (11 * (k + 1) + 2) + 2 = 10 * (11 * k + 2) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 2) + 2) = 2 ^ (10 * (11 * k + 2) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 2) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 24) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 677256111982803603721369086420012) + 24 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 2) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_2 k
  have hexp2 : 46 * m + 24 + 2 = 46 * m + 26 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 2) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 24 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 26) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 26 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 26 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 26 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 26 + 3 := by rw [one_pow]
    _ = 2 ^ 26 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_3 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 3) + 2) = 46 * m + 12 := by
  induction' k with k ih
  · use 93368854; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 338628055991401801860684543210006
    have hexp : 10 * (11 * (k + 1) + 3) + 2 = 10 * (11 * k + 3) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 3) + 2) = 2 ^ (10 * (11 * k + 3) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 3) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 12) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 338628055991401801860684543210006) + 12 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_3 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 3) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_3 k
  have hexp2 : 46 * m + 12 + 2 = 46 * m + 14 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 3) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 12 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 14) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 14 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 14 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 14 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 14 + 3 := by rw [one_pow]
    _ = 2 ^ 14 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_4 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 4) + 2) = 46 * m + 6 := by
  induction' k with k ih
  · use 95609706763; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 169314027995700900930342271605003
    have hexp : 10 * (11 * (k + 1) + 4) + 2 = 10 * (11 * k + 4) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 4) + 2) = 2 ^ (10 * (11 * k + 4) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 4) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 6) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 169314027995700900930342271605003) + 6 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_4 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 4) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_4 k
  have hexp2 : 46 * m + 6 + 2 = 46 * m + 8 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 4) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 6 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 8) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 8 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 8 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 8 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 8 + 3 := by rw [one_pow]
    _ = 2 ^ 8 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_5 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 5) + 2) = 46 * m + 26 := by
  induction' k with k ih
  · use 97904339725445; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 733694121314703904031483176955013
    have hexp : 10 * (11 * (k + 1) + 5) + 2 = 10 * (11 * k + 5) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 5) + 2) = 2 ^ (10 * (11 * k + 5) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 5) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 26) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 733694121314703904031483176955013) + 26 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_5 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 5) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_5 k
  have hexp2 : 46 * m + 26 + 2 = 46 * m + 28 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 5) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 26 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 28) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 28 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 28 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 28 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 28 + 3 := by rw [one_pow]
    _ = 2 ^ 28 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_6 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 6) + 2) = 46 * m + 36 := by
  induction' k with k ih
  · use 100254043878856258; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 1015884167974205405582053629630018
    have hexp : 10 * (11 * (k + 1) + 6) + 2 = 10 * (11 * k + 6) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 6) + 2) = 2 ^ (10 * (11 * k + 6) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 6) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 36) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 1015884167974205405582053629630018) + 36 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_6 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 6) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_6 k
  have hexp2 : 46 * m + 36 + 2 = 46 * m + 38 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 6) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 36 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 38) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 38 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 38 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 38 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 38 + 3 := by rw [one_pow]
    _ = 2 ^ 38 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_7 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 7) + 2) = 46 * m + 18 := by
  induction' k with k ih
  · use 102660140931948808993; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 507942083987102702791026814815009
    have hexp : 10 * (11 * (k + 1) + 7) + 2 = 10 * (11 * k + 7) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 7) + 2) = 2 ^ (10 * (11 * k + 7) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 7) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 18) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 507942083987102702791026814815009) + 18 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_7 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 7) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_7 k
  have hexp2 : 46 * m + 18 + 2 = 46 * m + 20 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 7) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 18 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 20) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 20 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 20 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 20 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 20 + 3 := by rw [one_pow]
    _ = 2 ^ 20 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_8 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 8) + 2) = 46 * m + 32 := by
  induction' k with k ih
  · use 105123984314315580409232; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 903008149310404804961825448560016
    have hexp : 10 * (11 * (k + 1) + 8) + 2 = 10 * (11 * k + 8) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 8) + 2) = 2 ^ (10 * (11 * k + 8) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 8) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 32) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 903008149310404804961825448560016) + 32 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_8 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 8) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_8 k
  have hexp2 : 46 * m + 32 + 2 = 46 * m + 34 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 8) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 32 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 34) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 34 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 34 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 34 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 34 + 3 := by rw [one_pow]
    _ = 2 ^ 34 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_9 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 9) + 2) = 46 * m + 16 := by
  induction' k with k ih
  · use 107646959937859154339054280; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 451504074655202402480912724280008
    have hexp : 10 * (11 * (k + 1) + 9) + 2 = 10 * (11 * k + 9) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 9) + 2) = 2 ^ (10 * (11 * k + 9) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 9) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 16) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 451504074655202402480912724280008) + 16 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_9 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 9) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_9 k
  have hexp2 : 46 * m + 16 + 2 = 46 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 9) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_exp_10 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (11 * k + 10) + 2) = 46 * m + 8 := by
  induction' k with k ih
  · use 110230486976367774043191583076; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1298074214633706907132624082305024 + 225752037327601201240456362140004
    have hexp : 10 * (11 * (k + 1) + 10) + 2 = 10 * (11 * k + 10) + 2 + 110 := by omega
    calc
      2 ^ (10 * (11 * (k + 1) + 10) + 2) = 2 ^ (10 * (11 * k + 10) + 2 + 110) := by rw [hexp]
      _ = 2 ^ (10 * (11 * k + 10) + 2) * 2 ^ 110 := by rw [pow_add]
      _ = (46 * m + 8) * 2 ^ 110 := by rw [hm]
      _ = 46 * (m * 1298074214633706907132624082305024 + 225752037327601201240456362140004) + 8 := by
        have h_mult : 2 ^ 110 = 1298074214633706907132624082305024 := by decide
        rw [h_mult]
        omega

lemma p47_not_dvd_10 (k : ℕ) : (2 ^ (2 ^ (10 * (11 * k + 10) + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have ⟨m, hm⟩ := p47_exp_10 k
  have hexp2 : 46 * m + 8 + 2 = 46 * m + 10 := by omega
  calc
    (2 ^ (2 ^ (10 * (11 * k + 10) + 2) + 2) + 3 : ZMod 47) = 2 ^ (46 * m + 8 + 2) + 3 := by rw [hm]
    _ = 2 ^ (46 * m + 10) + 3 := by rw [hexp2]
    _ = 2 ^ (46 * m) * 2 ^ 10 + 3 := by rw [pow_add]
    _ = (2 ^ 46) ^ m * 2 ^ 10 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 10 + 3 := by
      have h1 : (2 ^ 46 : ZMod 47) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 10 + 3 := by rw [one_pow]
    _ = 2 ^ 10 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p47_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 47) ≠ 0 := by
  have h_cases : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · have h_eq : n = 11 * (n / 11) + 0 := by omega
    rw [h_eq]
    exact p47_not_dvd_0 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 1 := by omega
    rw [h_eq]
    exact p47_not_dvd_1 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 2 := by omega
    rw [h_eq]
    exact p47_not_dvd_2 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 3 := by omega
    rw [h_eq]
    exact p47_not_dvd_3 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 4 := by omega
    rw [h_eq]
    exact p47_not_dvd_4 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 5 := by omega
    rw [h_eq]
    exact p47_not_dvd_5 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 6 := by omega
    rw [h_eq]
    exact p47_not_dvd_6 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 7 := by omega
    rw [h_eq]
    exact p47_not_dvd_7 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 8 := by omega
    rw [h_eq]
    exact p47_not_dvd_8 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 9 := by omega
    rw [h_eq]
    exact p47_not_dvd_9 (n / 11)
  · have h_eq : n = 11 * (n / 11) + 10 := by omega
    rw [h_eq]
    exact p47_not_dvd_10 (n / 11)

lemma p53_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 0) + 2) = 52 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 88686269585142075
    have hexp : 10 * (6 * (k + 1) + 0) + 2 = 10 * (6 * k + 0) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 0) + 2) = 2 ^ (10 * (6 * k + 0) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 0) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 4) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 88686269585142075) + 4 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 0) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_0 k
  have hexp2 : 52 * m + 4 + 2 = 52 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 0) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 1) + 2) = 52 * m + 40 := by
  induction' k with k ih
  · use 78; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 886862695851420750
    have hexp : 10 * (6 * (k + 1) + 1) + 2 = 10 * (6 * k + 1) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 1) + 2) = 2 ^ (10 * (6 * k + 1) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 1) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 40) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 886862695851420750) + 40 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 1) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_1 k
  have hexp2 : 52 * m + 40 + 2 = 52 * m + 42 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 1) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 40 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 42) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 42 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 42 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 42 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 42 + 3 := by rw [one_pow]
    _ = 2 ^ 42 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 2) + 2) = 52 * m + 36 := by
  induction' k with k ih
  · use 80659; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 798176426266278675
    have hexp : 10 * (6 * (k + 1) + 2) + 2 = 10 * (6 * k + 2) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 2) + 2) = 2 ^ (10 * (6 * k + 2) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 2) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 36) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 798176426266278675) + 36 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 2) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_2 k
  have hexp2 : 52 * m + 36 + 2 = 52 * m + 38 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 2) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 36 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 38) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 38 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 38 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 38 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 38 + 3 := by rw [one_pow]
    _ = 2 ^ 38 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_exp_3 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 3) + 2) = 52 * m + 48 := by
  induction' k with k ih
  · use 82595524; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 1064235235021704900
    have hexp : 10 * (6 * (k + 1) + 3) + 2 = 10 * (6 * k + 3) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 3) + 2) = 2 ^ (10 * (6 * k + 3) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 3) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 48) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 1064235235021704900) + 48 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_3 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 3) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_3 k
  have hexp2 : 52 * m + 48 + 2 = 52 * m + 50 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 3) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 48 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 50) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 50 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 50 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 50 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 50 + 3 := by rw [one_pow]
    _ = 2 ^ 50 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_exp_4 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 4) + 2) = 52 * m + 12 := by
  induction' k with k ih
  · use 84577817521; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 266058808755426225
    have hexp : 10 * (6 * (k + 1) + 4) + 2 = 10 * (6 * k + 4) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 4) + 2) = 2 ^ (10 * (6 * k + 4) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 4) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 12) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 266058808755426225) + 12 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_4 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 4) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_4 k
  have hexp2 : 52 * m + 12 + 2 = 52 * m + 14 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 4) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 12 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 14) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 14 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 14 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 14 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 14 + 3 := by rw [one_pow]
    _ = 2 ^ 14 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_exp_5 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (6 * k + 5) + 2) = 52 * m + 16 := by
  induction' k with k ih
  · use 86607685141740; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1152921504606846976 + 354745078340568300
    have hexp : 10 * (6 * (k + 1) + 5) + 2 = 10 * (6 * k + 5) + 2 + 60 := by omega
    calc
      2 ^ (10 * (6 * (k + 1) + 5) + 2) = 2 ^ (10 * (6 * k + 5) + 2 + 60) := by rw [hexp]
      _ = 2 ^ (10 * (6 * k + 5) + 2) * 2 ^ 60 := by rw [pow_add]
      _ = (52 * m + 16) * 2 ^ 60 := by rw [hm]
      _ = 52 * (m * 1152921504606846976 + 354745078340568300) + 16 := by
        have h_mult : 2 ^ 60 = 1152921504606846976 := by decide
        rw [h_mult]
        omega

lemma p53_not_dvd_5 (k : ℕ) : (2 ^ (2 ^ (10 * (6 * k + 5) + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have ⟨m, hm⟩ := p53_exp_5 k
  have hexp2 : 52 * m + 16 + 2 = 52 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (6 * k + 5) + 2) + 2) + 3 : ZMod 53) = 2 ^ (52 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (52 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (52 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 52) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 52 : ZMod 53) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p53_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 53) ≠ 0 := by
  have h_cases : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5
  · have h_eq : n = 6 * (n / 6) + 0 := by omega
    rw [h_eq]
    exact p53_not_dvd_0 (n / 6)
  · have h_eq : n = 6 * (n / 6) + 1 := by omega
    rw [h_eq]
    exact p53_not_dvd_1 (n / 6)
  · have h_eq : n = 6 * (n / 6) + 2 := by omega
    rw [h_eq]
    exact p53_not_dvd_2 (n / 6)
  · have h_eq : n = 6 * (n / 6) + 3 := by omega
    rw [h_eq]
    exact p53_not_dvd_3 (n / 6)
  · have h_eq : n = 6 * (n / 6) + 4 := by omega
    rw [h_eq]
    exact p53_not_dvd_4 (n / 6)
  · have h_eq : n = 6 * (n / 6) + 5 := by omega
    rw [h_eq]
    exact p53_not_dvd_5 (n / 6)

lemma p59_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 0) + 2) = 58 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 96123901717804410092826371864863627180950
    have hexp : 10 * (14 * (k + 1) + 0) + 2 = 10 * (14 * k + 0) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 0) + 2) = 2 ^ (10 * (14 * k + 0) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 0) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 4) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 96123901717804410092826371864863627180950) + 4 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 0) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_0 k
  have hexp2 : 58 * m + 4 + 2 = 58 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 0) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 1) + 2) = 58 * m + 36 := by
  induction' k with k ih
  · use 70; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 865115115460239690835437346783772644628550
    have hexp : 10 * (14 * (k + 1) + 1) + 2 = 10 * (14 * k + 1) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 1) + 2) = 2 ^ (10 * (14 * k + 1) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 1) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 36) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 865115115460239690835437346783772644628550) + 36 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 1) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_1 k
  have hexp2 : 58 * m + 36 + 2 = 58 * m + 38 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 1) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 36 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 38) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 38 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 38 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 38 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 38 + 3 := by rw [one_pow]
    _ = 2 ^ 38 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_2 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 2) + 2) = 58 * m + 34 := by
  induction' k with k ih
  · use 72315; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 817053164601337485789024160851340831038075
    have hexp : 10 * (14 * (k + 1) + 2) + 2 = 10 * (14 * k + 2) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 2) + 2) = 2 ^ (10 * (14 * k + 2) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 2) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 34) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 817053164601337485789024160851340831038075) + 34 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_2 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 2) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_2 k
  have hexp2 : 58 * m + 34 + 2 = 58 * m + 36 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 2) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 34 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 36) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 36 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 36 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 36 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 36 + 3 := by rw [one_pow]
    _ = 2 ^ 36 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_3 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 3) + 2) = 58 * m + 16 := by
  induction' k with k ih
  · use 74051160; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 384495606871217640371305487459454508723800
    have hexp : 10 * (14 * (k + 1) + 3) + 2 = 10 * (14 * k + 3) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 3) + 2) = 2 ^ (10 * (14 * k + 3) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 3) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 16) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 384495606871217640371305487459454508723800) + 16 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_3 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 3) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_3 k
  have hexp2 : 58 * m + 16 + 2 = 58 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 3) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_4 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 4) + 2) = 58 * m + 28 := by
  induction' k with k ih
  · use 75828388122; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 672867312024630870649784603054045390266650
    have hexp : 10 * (14 * (k + 1) + 4) + 2 = 10 * (14 * k + 4) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 4) + 2) = 2 ^ (10 * (14 * k + 4) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 4) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 28) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 672867312024630870649784603054045390266650) + 28 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_4 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 4) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_4 k
  have hexp2 : 58 * m + 28 + 2 = 58 * m + 30 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 4) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 28 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 30) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 30 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 30 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 30 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 30 + 3 := by rw [one_pow]
    _ = 2 ^ 30 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_5 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 5) + 2) = 58 * m + 20 := by
  induction' k with k ih
  · use 77648269437422; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 480619508589022050464131859324318135904750
    have hexp : 10 * (14 * (k + 1) + 5) + 2 = 10 * (14 * k + 5) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 5) + 2) = 2 ^ (10 * (14 * k + 5) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 5) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 20) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 480619508589022050464131859324318135904750) + 20 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_5 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 5) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_5 k
  have hexp2 : 58 * m + 20 + 2 = 58 * m + 22 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 5) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 20 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 22) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 22 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 22 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 22 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 22 + 3 := by rw [one_pow]
    _ = 2 ^ 22 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_6 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 6) + 2) = 58 * m + 6 := by
  induction' k with k ih
  · use 79511827903920481; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 144185852576706615139239557797295440771425
    have hexp : 10 * (14 * (k + 1) + 6) + 2 = 10 * (14 * k + 6) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 6) + 2) = 2 ^ (10 * (14 * k + 6) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 6) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 6) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 144185852576706615139239557797295440771425) + 6 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_6 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 6) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_6 k
  have hexp2 : 58 * m + 6 + 2 = 58 * m + 8 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 6) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 6 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 8) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 8 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 8 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 8 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 8 + 3 := by rw [one_pow]
    _ = 2 ^ 8 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_7 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 7) + 2) = 58 * m + 54 := by
  induction' k with k ih
  · use 81420111773614572649; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 1297672673190359536253156020175658966942825
    have hexp : 10 * (14 * (k + 1) + 7) + 2 = 10 * (14 * k + 7) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 7) + 2) = 2 ^ (10 * (14 * k + 7) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 7) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 54) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 1297672673190359536253156020175658966942825) + 54 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_7 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 7) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_7 k
  have hexp2 : 58 * m + 54 + 2 = 58 * m + 56 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 7) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 54 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 56) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 56 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 56 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 56 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 56 + 3 := by rw [one_pow]
    _ = 2 ^ 56 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_8 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 8) + 2) = 58 * m + 22 := by
  induction' k with k ih
  · use 83374194456181322393529; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 528681459447924255510545045256749949495225
    have hexp : 10 * (14 * (k + 1) + 8) + 2 = 10 * (14 * k + 8) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 8) + 2) = 2 ^ (10 * (14 * k + 8) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 8) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 22) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 528681459447924255510545045256749949495225) + 22 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_8 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 8) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_8 k
  have hexp2 : 58 * m + 22 + 2 = 58 * m + 24 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 8) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 22 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 24) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 24 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 24 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 24 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 24 + 3 := by rw [one_pow]
    _ = 2 ^ 24 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_9 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 9) + 2) = 58 * m + 24 := by
  induction' k with k ih
  · use 85375175123129674130974084; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 576743410306826460556958231189181763085700
    have hexp : 10 * (14 * (k + 1) + 9) + 2 = 10 * (14 * k + 9) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 9) + 2) = 2 ^ (10 * (14 * k + 9) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 9) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 24) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 576743410306826460556958231189181763085700) + 24 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_9 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 9) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_9 k
  have hexp2 : 58 * m + 24 + 2 = 58 * m + 26 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 9) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 24 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 26) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 26 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 26 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 26 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 26 + 3 := by rw [one_pow]
    _ = 2 ^ 26 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_10 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 10) + 2) = 58 * m + 42 := by
  induction' k with k ih
  · use 87424179326084786310117462439; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 1009300968036946305974676904581068085399975
    have hexp : 10 * (14 * (k + 1) + 10) + 2 = 10 * (14 * k + 10) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 10) + 2) = 2 ^ (10 * (14 * k + 10) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 10) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 42) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 1009300968036946305974676904581068085399975) + 42 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_10 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 10) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_10 k
  have hexp2 : 58 * m + 42 + 2 = 58 * m + 44 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 10) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 42 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 44) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 44 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 44 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 44 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 44 + 3 := by rw [one_pow]
    _ = 2 ^ 44 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_11 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 11) + 2) = 58 * m + 30 := by
  induction' k with k ih
  · use 89522359629910821181560281538277; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 720929262883533075696197788986477203857125
    have hexp : 10 * (14 * (k + 1) + 11) + 2 = 10 * (14 * k + 11) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 11) + 2) = 2 ^ (10 * (14 * k + 11) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 11) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 30) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 720929262883533075696197788986477203857125) + 30 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_11 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 11) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_11 k
  have hexp2 : 58 * m + 30 + 2 = 58 * m + 32 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 11) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 30 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 32) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 32 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 32 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 32 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 32 + 3 := by rw [one_pow]
    _ = 2 ^ 32 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_12 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 12) + 2) = 58 * m + 38 := by
  induction' k with k ih
  · use 91670896261028680889917728295196177; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 913177066319141895881850532716204458219025
    have hexp : 10 * (14 * (k + 1) + 12) + 2 = 10 * (14 * k + 12) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 12) + 2) = 2 ^ (10 * (14 * k + 12) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 12) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 38) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 913177066319141895881850532716204458219025) + 38 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_12 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 12) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_12 k
  have hexp2 : 58 * m + 38 + 2 = 58 * m + 40 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 12) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 38 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 40) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 40 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 40 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 40 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 40 + 3 := by rw [one_pow]
    _ = 2 ^ 40 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_exp_13 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (14 * k + 13) + 2) = 58 * m + 52 := by
  induction' k with k ih
  · use 93870997771293369231275753774280885918; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1393796574908163946345982392040522594123776 + 1249610722331457331206742834243227153352350
    have hexp : 10 * (14 * (k + 1) + 13) + 2 = 10 * (14 * k + 13) + 2 + 140 := by omega
    calc
      2 ^ (10 * (14 * (k + 1) + 13) + 2) = 2 ^ (10 * (14 * k + 13) + 2 + 140) := by rw [hexp]
      _ = 2 ^ (10 * (14 * k + 13) + 2) * 2 ^ 140 := by rw [pow_add]
      _ = (58 * m + 52) * 2 ^ 140 := by rw [hm]
      _ = 58 * (m * 1393796574908163946345982392040522594123776 + 1249610722331457331206742834243227153352350) + 52 := by
        have h_mult : 2 ^ 140 = 1393796574908163946345982392040522594123776 := by decide
        rw [h_mult]
        omega

lemma p59_not_dvd_13 (k : ℕ) : (2 ^ (2 ^ (10 * (14 * k + 13) + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have ⟨m, hm⟩ := p59_exp_13 k
  have hexp2 : 58 * m + 52 + 2 = 58 * m + 54 := by omega
  calc
    (2 ^ (2 ^ (10 * (14 * k + 13) + 2) + 2) + 3 : ZMod 59) = 2 ^ (58 * m + 52 + 2) + 3 := by rw [hm]
    _ = 2 ^ (58 * m + 54) + 3 := by rw [hexp2]
    _ = 2 ^ (58 * m) * 2 ^ 54 + 3 := by rw [pow_add]
    _ = (2 ^ 58) ^ m * 2 ^ 54 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 54 + 3 := by
      have h1 : (2 ^ 58 : ZMod 59) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 54 + 3 := by rw [one_pow]
    _ = 2 ^ 54 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p59_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 59) ≠ 0 := by
  have h_cases : n % 14 = 0 ∨ n % 14 = 1 ∨ n % 14 = 2 ∨ n % 14 = 3 ∨ n % 14 = 4 ∨ n % 14 = 5 ∨ n % 14 = 6 ∨ n % 14 = 7 ∨ n % 14 = 8 ∨ n % 14 = 9 ∨ n % 14 = 10 ∨ n % 14 = 11 ∨ n % 14 = 12 ∨ n % 14 = 13 := by omega
  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · have h_eq : n = 14 * (n / 14) + 0 := by omega
    rw [h_eq]
    exact p59_not_dvd_0 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 1 := by omega
    rw [h_eq]
    exact p59_not_dvd_1 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 2 := by omega
    rw [h_eq]
    exact p59_not_dvd_2 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 3 := by omega
    rw [h_eq]
    exact p59_not_dvd_3 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 4 := by omega
    rw [h_eq]
    exact p59_not_dvd_4 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 5 := by omega
    rw [h_eq]
    exact p59_not_dvd_5 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 6 := by omega
    rw [h_eq]
    exact p59_not_dvd_6 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 7 := by omega
    rw [h_eq]
    exact p59_not_dvd_7 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 8 := by omega
    rw [h_eq]
    exact p59_not_dvd_8 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 9 := by omega
    rw [h_eq]
    exact p59_not_dvd_9 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 10 := by omega
    rw [h_eq]
    exact p59_not_dvd_10 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 11 := by omega
    rw [h_eq]
    exact p59_not_dvd_11 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 12 := by omega
    rw [h_eq]
    exact p59_not_dvd_12 (n / 14)
  · have h_eq : n = 14 * (n / 14) + 13 := by omega
    rw [h_eq]
    exact p59_not_dvd_13 (n / 14)

lemma p61_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 0) + 2) = 60 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 69905
    have hexp : 10 * (2 * (k + 1) + 0) + 2 = 10 * (2 * k + 0) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 0) + 2) = 2 ^ (10 * (2 * k + 0) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 0) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (60 * m + 4) * 2 ^ 20 := by rw [hm]
      _ = 60 * (m * 1048576 + 69905) + 4 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p61_not_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 61) ≠ 0 := by
  have ⟨m, hm⟩ := p61_exp_0 k
  have hexp2 : 60 * m + 4 + 2 = 60 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 0) + 2) + 2) + 3 : ZMod 61) = 2 ^ (60 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (60 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (60 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 60) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 60 : ZMod 61) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p61_exp_1 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (2 * k + 1) + 2) = 60 * m + 16 := by
  induction' k with k ih
  · use 68; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1048576 + 279620
    have hexp : 10 * (2 * (k + 1) + 1) + 2 = 10 * (2 * k + 1) + 2 + 20 := by omega
    calc
      2 ^ (10 * (2 * (k + 1) + 1) + 2) = 2 ^ (10 * (2 * k + 1) + 2 + 20) := by rw [hexp]
      _ = 2 ^ (10 * (2 * k + 1) + 2) * 2 ^ 20 := by rw [pow_add]
      _ = (60 * m + 16) * 2 ^ 20 := by rw [hm]
      _ = 60 * (m * 1048576 + 279620) + 16 := by
        have h_mult : 2 ^ 20 = 1048576 := by decide
        rw [h_mult]
        omega

lemma p61_not_dvd_1 (k : ℕ) : (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 61) ≠ 0 := by
  have ⟨m, hm⟩ := p61_exp_1 k
  have hexp2 : 60 * m + 16 + 2 = 60 * m + 18 := by omega
  calc
    (2 ^ (2 ^ (10 * (2 * k + 1) + 2) + 2) + 3 : ZMod 61) = 2 ^ (60 * m + 16 + 2) + 3 := by rw [hm]
    _ = 2 ^ (60 * m + 18) + 3 := by rw [hexp2]
    _ = 2 ^ (60 * m) * 2 ^ 18 + 3 := by rw [pow_add]
    _ = (2 ^ 60) ^ m * 2 ^ 18 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 18 + 3 := by
      have h1 : (2 ^ 60 : ZMod 61) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 18 + 3 := by rw [one_pow]
    _ = 2 ^ 18 + 3 := by rw [one_mul]
    _ ≠ 0 := by decide

lemma p61_not_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 61) ≠ 0 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · have h_eq : n = 2 * (n / 2) + 0 := by omega
    rw [h_eq]
    exact p61_not_dvd_0 (n / 2)
  · have h_eq : n = 2 * (n / 2) + 1 := by omega
    rw [h_eq]
    exact p61_not_dvd_1 (n / 2)

lemma p67_exp_0 (k : ℕ) : ∃ m : ℕ, 2 ^ (10 * (1 * k + 0) + 2) = 66 * m + 4 := by
  induction' k with k ih
  · use 0; rfl
  · rcases ih with ⟨m, hm⟩
    use m * 1024 + 62
    have hexp : 10 * (1 * (k + 1) + 0) + 2 = 10 * (1 * k + 0) + 2 + 10 := by omega
    calc
      2 ^ (10 * (1 * (k + 1) + 0) + 2) = 2 ^ (10 * (1 * k + 0) + 2 + 10) := by rw [hexp]
      _ = 2 ^ (10 * (1 * k + 0) + 2) * 2 ^ 10 := by rw [pow_add]
      _ = (66 * m + 4) * 2 ^ 10 := by rw [hm]
      _ = 66 * (m * 1024 + 62) + 4 := by
        have h_mult : 2 ^ 10 = 1024 := by decide
        rw [h_mult]
        omega

lemma p67_is_dvd_0 (k : ℕ) : (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 67) = 0 := by
  have ⟨m, hm⟩ := p67_exp_0 k
  have hexp2 : 66 * m + 4 + 2 = 66 * m + 6 := by omega
  calc
    (2 ^ (2 ^ (10 * (1 * k + 0) + 2) + 2) + 3 : ZMod 67) = 2 ^ (66 * m + 4 + 2) + 3 := by rw [hm]
    _ = 2 ^ (66 * m + 6) + 3 := by rw [hexp2]
    _ = 2 ^ (66 * m) * 2 ^ 6 + 3 := by rw [pow_add]
    _ = (2 ^ 66) ^ m * 2 ^ 6 + 3 := by rw [pow_mul]
    _ = 1 ^ m * 2 ^ 6 + 3 := by
      have h1 : (2 ^ 66 : ZMod 67) = 1 := by decide
      rw [h1]
    _ = 1 * 2 ^ 6 + 3 := by rw [one_pow]
    _ = 2 ^ 6 + 3 := by rw [one_mul]
    _ = 0 := by decide

lemma p67_is_dvd (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ZMod 67) = 0 := by
  have h_eq : n = 1 * n + 0 := by omega
  rw [h_eq]
  exact p67_is_dvd_0 n

