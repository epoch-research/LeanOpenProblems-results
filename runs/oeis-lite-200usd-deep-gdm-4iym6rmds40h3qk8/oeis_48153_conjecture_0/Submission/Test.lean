import FormalConjectures.Util.ProblemImports

lemma Nat.sq_sub_add_mul_self (n k : ℕ) (h : k ≤ n) :
    (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := by
  have h_int : ((n - k : ℕ) : ℤ) ^ 2 + 2 * (n : ℤ) * (k : ℤ) = (n : ℤ) ^ 2 + (k : ℤ) ^ 2 := by
    rw [Nat.cast_sub h]
    ring
  exact_mod_cast h_int

lemma sq_sub_mod (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have h1 : (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := Nat.sq_sub_add_mul_self n k h
  have h2 : ((n - k) ^ 2 + 2 * n * k) % n = (n ^ 2 + k ^ 2) % n := by rw [h1]
  have hLHS : ((n - k) ^ 2 + 2 * n * k) % n = (n - k) ^ 2 % n := by
    have : 2 * n * k = n * (2 * k) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  have hRHS : (n ^ 2 + k ^ 2) % n = k ^ 2 % n := by
    have : n ^ 2 + k ^ 2 = k ^ 2 + n * n := by ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [hLHS, hRHS] at h2
  exact h2

lemma sq_mod_le_mul_div (n k : ℕ) (h : k < n) : k ^ 2 % n ≤ k * n / 2 := by
  by_cases h_le : k * 2 ≤ n
  · have h1 : k ^ 2 % n ≤ k ^ 2 := Nat.mod_le (k ^ 2) n
    have h2 : 2 * (k ^ 2 % n) ≤ k * n := by
      calc 2 * (k ^ 2 % n) ≤ 2 * k ^ 2 := by omega
      _ = k * (2 * k) := by ring
      _ ≤ k * n := by
        have : 2 * k ≤ n := by omega
        exact Nat.mul_le_mul_left k this
    omega
  · push_neg at h_le
    have h_sub_le : 2 * (n - k) ≤ n := by omega
    have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
    have h_mod_le : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le _ _
    have h2 : 2 * ((n - k) ^ 2 % n) ≤ (n - k) * n := by
      calc 2 * ((n - k) ^ 2 % n) ≤ 2 * (n - k) ^ 2 := by omega
      _ = (n - k) * (2 * (n - k)) := by ring
      _ ≤ (n - k) * n := Nat.mul_le_mul_left (n - k) h_sub_le
    have h_mul_le : (n - k) * n ≤ k * n := Nat.mul_le_mul_right n (by omega)
    have h3 : 2 * ((n - k) ^ 2 % n) ≤ k * n := Nat.le_trans h2 h_mul_le
    rw [h1]
    omega

lemma sq_mod_le_sub_mul_div (n k : ℕ) (h : k < n) : k ^ 2 % n ≤ (n - k) * (n - 1) / 2 := by
  by_cases h_le : (n - k) * 2 ≤ n - 1
  · have h1 : k ^ 2 % n = (n - k) ^ 2 % n := (sq_sub_mod n k (by omega)).symm
    have h_mod_le : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le _ _
    have h2 : 2 * ((n - k) ^ 2 % n) ≤ (n - k) * (n - 1) := by
      calc 2 * ((n - k) ^ 2 % n) ≤ 2 * (n - k) ^ 2 := by omega
      _ = (n - k) * (2 * (n - k)) := by ring
      _ ≤ (n - k) * (n - 1) := by
        have : 2 * (n - k) ≤ n - 1 := by omega
        exact Nat.mul_le_mul_left (n - k) this
    rw [h1]
    omega
  · push_neg at h_le
    have h_sub_le : 2 * k ≤ n - 1 := by omega
    have h_mod_le : k ^ 2 % n ≤ k ^ 2 := Nat.mod_le _ _
    have h2 : 2 * (k ^ 2 % n) ≤ k * (n - 1) := by
      calc 2 * (k ^ 2 % n) ≤ 2 * k ^ 2 := by omega
      _ = k * (2 * k) := by ring
      _ ≤ k * (n - 1) := Nat.mul_le_mul_left k h_sub_le
    have h_mul_le : k * (n - 1) ≤ (n - k) * (n - 1) := Nat.mul_le_mul_right (n - 1) (by omega)
    have h3 : 2 * (k ^ 2 % n) ≤ (n - k) * (n - 1) := Nat.le_trans h2 h_mul_le
    omega


lemma sq_mod_le_sub_one (n k : ℕ) (h : 1 ≤ n) : k ^ 2 % n ≤ n - 1 := by
  have : k ^ 2 % n < n := Nat.mod_lt _ h
  omega





lemma mod_add_mod_eq_zero_or_n (n a b : ℕ) (hn : 0 < n) (h : (a + b) % n = 0) : a % n + b % n = 0 ∨ a % n + b % n = n := by
  have h1 : a % n < n := Nat.mod_lt a hn
  have h2 : b % n < n := Nat.mod_lt b hn
  have h3 : (a % n + b % n) % n = 0 := by
    rw [← Nat.add_mod, h]
  omega
