import FormalConjectures.Util.ProblemImports

lemma bound_linear (n : ℕ) : 2 * n + 3 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_eq : 2 * (n + 1) + 3 = (2 * n + 3) + 2 := by omega
    rw [h_eq]
    have h_pow : 2 ^ (n + 1 + 2) = 2 ^ (n + 2) + 2 ^ (n + 2) := by
      have : n + 1 + 2 = n + 2 + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h_pow]
    have h_two : 2 ≤ 2 ^ (n + 2) := by
      have h_pow_eq : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this, pow_succ]
      rw [h_pow_eq]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by decide)
      omega
    omega

lemma bound_quadratic (n : ℕ) : 1 + (n + 1)^2 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_eq : 1 + (n + 1 + 1)^2 = 1 + (n + 1)^2 + 2 * n + 3 := by ring
    rw [h_eq]
    have h_pow : 2 ^ (n + 1 + 2) = 2 ^ (n + 2) + 2 ^ (n + 2) := by
      have : n + 1 + 2 = n + 2 + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h_pow]
    have h_lin := bound_linear n
    omega


def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

lemma norm_le_power (n : ℕ) : (P n).1^2 + (P n).2^2 ≤ (2 : ℤ)^(n^2 + 3 * n + 1) := by
  induction n with
  | zero =>
    simp [P]
  | succ n ih =>
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + (n + 1 : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    have h_bound : 1 + (n + 1 : ℤ)^2 ≤ (2 : ℤ)^(n + 2) := by
      have hq := bound_quadratic n
      exact_mod_cast hq
    have h_pos_norm : (P n).1^2 + (P n).2^2 ≥ 0 := by positivity
    have h_pos_bound : (2 : ℤ)^(n + 2) ≥ 0 := by positivity
    have h_mul : (1 + (n + 1 : ℤ)^2) * ((P n).1^2 + (P n).2^2) ≤ (2 : ℤ)^(n + 2) * (2 : ℤ)^(n^2 + 3 * n + 1) := by
      apply mul_le_mul h_bound ih h_pos_norm h_pos_bound
    have h_pow : (2 : ℤ)^(n + 2) * (2 : ℤ)^(n^2 + 3 * n + 1) = (2 : ℤ)^(n^2 + 4 * n + 3) := by
      rw [← pow_add]
      congr 1
      ring
    have h_le : (2 : ℤ)^(n^2 + 4 * n + 3) ≤ (2 : ℤ)^((n + 1)^2 + 3 * (n + 1) + 1) := by
      have h_exp : n^2 + 4 * n + 3 ≤ (n + 1)^2 + 3 * (n + 1) + 1 := by ring_nf; omega
      have h_nat : 2^(n^2 + 4 * n + 3) ≤ 2^((n + 1)^2 + 3 * (n + 1) + 1) := Nat.pow_le_pow_right (by decide) h_exp
      exact_mod_cast h_nat
    rw [h_pow] at h_mul
    exact le_trans h_mul h_le
