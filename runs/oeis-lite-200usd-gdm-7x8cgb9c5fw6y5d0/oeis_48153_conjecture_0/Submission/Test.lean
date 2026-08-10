import FormalConjectures.Util.ProblemImports

lemma k_sq_div_ge_six_linear (m k : ℕ) : 6 * k - (3 * m + 6) ≤ 6 * (k^2 / (2*m+1)) := by
  have hn : 1 ≤ 2*m+1 := by omega
  by_cases hk : 6 * k ≤ 3 * m + 6
  · have : 6 * k - (3 * m + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) (2*m+1)
    have h_mod : k^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ (by omega)
    omega

lemma k_sq_div_ge_six_linear_even (m k : ℕ) : 6 * k - (3 * m + 6) ≤ 6 * (k^2 / (2*m)) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hn : 1 ≤ 2*m := by omega
    by_cases hk : 6 * k ≤ 3 * m + 6
    · have : 6 * k - (3 * m + 6) = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h_div := Nat.div_add_mod (k^2) (2*m)
      have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ (by omega)
      omega

lemma n_minus_one_sq_div (n : ℕ) (hn : 2 ≤ n) : (n-1)^2 / n = n - 2 := by
  have h1 : (n-1)^2 = n * (n-2) + 1 := by omega
  rw [h1]
  rw [Nat.add_div (by omega)]
  -- omega or just simplify
  omega

lemma mul_sub_twelve_eq (m k : ℕ) : 12 * k - (12 * m + 6) = 12 * (k - m) - 6 := by omega

lemma mul_sub_six_eq (m k : ℕ) : 6 * k - (3 * m + 6) = 6 * (k - (m/2 + 1)) := by omega

lemma sum_sub_T_eq (T m : ℕ) (h : T ≤ m) :
  2 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T) = (m - T) * (m - T + 1) := by
  have h1 : Finset.Ico 1 (m+1) = Finset.Ico 1 (T+1) ∪ Finset.Ico (T+1) (m+1) := by
    rw [Finset.Ico_union_Ico (by omega) (by omega)]
  have h2 : Disjoint (Finset.Ico 1 (T+1)) (Finset.Ico (T+1) (m+1)) := by
    apply Finset.disjoint_iff_ne.mpr
    intro a ha b hb
    rw [Finset.mem_Ico] at ha hb
    omega
  have h3 : ∑ k ∈ Finset.Ico 1 (m+1), (k - T) = ∑ k ∈ Finset.Ico 1 (T+1), (k - T) + ∑ k ∈ Finset.Ico (T+1) (m+1), (k - T) := by
    rw [h1, Finset.sum_union h2]
  have h4 : ∑ k ∈ Finset.Ico 1 (T+1), (k - T) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  rw [h4, zero_add] at h3
  have h5 : ∑ k ∈ Finset.Ico (T+1) (m+1), (k - T) = ∑ x ∈ Finset.range (m - T), (x + 1) := by
    have h_shift := Finset.sum_Ico_add' (fun x => x - T) 0 (m - T) (T+1)
    have h_add : 0 + (T+1) = T+1 := by omega
    have h_add2 : m - T + (T+1) = m+1 := by omega
    rw [h_add, h_add2] at h_shift
    rw [h_shift]
    rw [Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro x _
    omega
  rw [h3, h5, mul_sum]
  rw [sum_add_distrib]
  rw [← mul_sum]
  rw [sum_range_id_mul_two]
  rw [sum_const, card_range, smul_eq_mul, mul_one]
  rcases m - T with _ | k
  · simp
  · ring


lemma k_sq_div_ge_six_linear_all (n k : ℕ) (hn : 1 ≤ n) : 6 * k - (3 * n + 6) ≤ 6 * (k^2 / n) := by
  by_cases hk : 6 * k ≤ 3 * n + 6
  · have : 6 * k - (3 * n + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) n
    have h_mod : k^2 % n < n := Nat.mod_lt _ hn
    omega


lemma k_sq_div_ge_twelve_linear (n k : ℕ) (hn : 1 ≤ n) : 12 * k - (6 * n + 6) ≤ 6 * (k^2 / n) := by
  by_cases hk : 12 * k ≤ 6 * n + 6
  · have : 12 * k - (6 * n + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) n
    have h_mod : k^2 % n < n := Nat.mod_lt _ hn
    omega

lemma k_sq_div_ge_twelve_linear_odd (m k : ℕ) : 12 * k - (12 * m + 6) ≤ 6 * (k^2 / (2*m+1)) := by
  have hn : 1 ≤ 2*m+1 := by omega
  by_cases hk : 12 * k ≤ 12 * m + 6
  · have : 12 * k - (12 * m + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) (2*m+1)
    have h_mod : k^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ hn
    omega


lemma k_sq_div_ge_twelve_linear_even (m k : ℕ) : 24 * k - (24 * m + 12) ≤ 12 * (k^2 / (2*m)) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hn : 1 ≤ 2*m := by omega
    by_cases hk : 24 * k ≤ 24 * m + 12
    · have : 24 * k - (24 * m + 12) = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h_div := Nat.div_add_mod (k^2) (2*m)
      have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ hn
      omega


lemma k_sq_div_ge_eight_linear (n k : ℕ) (hn : 1 ≤ n) : 8 * k - (3 * n + 6) ≤ 6 * (k^2 / n) := by
  by_cases hk : 8 * k ≤ 3 * n + 6
  · have : 8 * k - (3 * n + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) n
    have h_mod : k^2 % n < n := Nat.mod_lt _ hn
    omega



lemma k_sq_div_ge_five_linear (n k : ℕ) (hn : 1 ≤ n) : 5 * k - 2 * n ≤ 6 * (k^2 / n) := by
  by_cases hk : 5 * k ≤ 2 * n
  · have : 5 * k - 2 * n = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) n
    have h_mod : k^2 % n < n := Nat.mod_lt _ hn
    omega


lemma k_sq_div_ge_six_linear_odd (m k : ℕ) : 6 * k - (6 * m + 6) ≤ 6 * (k^2 / (2*m+1)) := by
  have hn : 1 ≤ 2*m+1 := by omega
  by_cases hk : 6 * k ≤ 6 * m + 6
  · have : 6 * k - (6 * m + 6) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) (2*m+1)
    have h_mod : k^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ hn
    omega


lemma k_sq_div_ge_six_linear_even_better (m k : ℕ) : 6 * k - (6 * m + 6) ≤ 6 * (k^2 / (2*m)) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hn : 1 ≤ 2*m := by omega
    by_cases hk : 6 * k ≤ 6 * m + 6
    · have : 6 * k - (6 * m + 6) = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h_div := Nat.div_add_mod (k^2) (2*m)
      have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ hn
      omega

lemma sum_sub_T_eq_even (T m : ℕ) (h : T < m) :
  2 * ∑ k ∈ Finset.Ico 1 m, (k - T) = (m - 1 - T) * (m - T) := by
  have h1 : Finset.Ico 1 m = Finset.Ico 1 (T+1) ∪ Finset.Ico (T+1) m := by
    rw [Finset.Ico_union_Ico (by omega) (by omega)]
  have h2 : Disjoint (Finset.Ico 1 (T+1)) (Finset.Ico (T+1) m) := by
    apply Finset.disjoint_iff_ne.mpr
    intro a ha b hb
    rw [Finset.mem_Ico] at ha hb
    omega
  have h3 : ∑ k ∈ Finset.Ico 1 m, (k - T) = ∑ k ∈ Finset.Ico 1 (T+1), (k - T) + ∑ k ∈ Finset.Ico (T+1) m, (k - T) := by
    rw [h1, Finset.sum_union h2]
  have h4 : ∑ k ∈ Finset.Ico 1 (T+1), (k - T) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  rw [h4, zero_add] at h3
  have h5 : ∑ k ∈ Finset.Ico (T+1) m, (k - T) = ∑ x ∈ Finset.range (m - 1 - T), (x + 1) := by
    have h_shift := Finset.sum_Ico_add' (fun x => x - T) 0 (m - 1 - T) (T+1)
    have h_add : 0 + (T+1) = T+1 := by omega
    have h_add2 : m - 1 - T + (T+1) = m := by omega
    rw [h_add, h_add2] at h_shift
    rw [h_shift]
    rw [Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro x _
    omega
  rw [h3, h5, mul_sum]
  rw [sum_add_distrib]
  rw [← mul_sum]
  rw [sum_range_id_mul_two]
  rw [sum_const, card_range, smul_eq_mul, mul_one]
  rcases m - 1 - T with _ | k
  · simp
  · ring


lemma twelve_sub_le (m k : ℕ) : 12 * (k - (m/2 + 1)) ≤ 12 * k - (6 * m + 12) := by omega


lemma k_sq_div_ge_eight_linear_odd (m k : ℕ) : 8 * k - (4 * m + 8) ≤ 6 * (k^2 / (2*m+1)) := by
  have hn : 1 ≤ 2*m+1 := by omega
  by_cases hk : 8 * k ≤ 4 * m + 8
  · have : 8 * k - (4 * m + 8) = 0 := by omega
    rw [this]
    exact Nat.zero_le _
  · have h_div := Nat.div_add_mod (k^2) (2*m+1)
    have h_mod : k^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ hn
    omega


lemma k_sq_div_ge_twelve_linear_even_better2 (m k : ℕ) : 12 * k - (6 * m + 12) ≤ 12 * (k^2 / (2*m)) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hn : 1 ≤ 2*m := by omega
    by_cases hk : 12 * k ≤ 6 * m + 12
    · have : 12 * k - (6 * m + 12) = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h_div := Nat.div_add_mod (k^2) (2*m)
      have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ hn
      omega


lemma k_sq_div_ge_fourteen_linear_even (m k : ℕ) : 14 * k - (6 * m + 12) ≤ 12 * (k^2 / (2*m)) := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hn : 1 ≤ 2*m := by omega
    by_cases hk : 14 * k ≤ 6 * m + 12
    · have : 14 * k - (6 * m + 12) = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h_div := Nat.div_add_mod (k^2) (2*m)
      have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ hn
      omega


lemma mul_sub_dist_n (n k : ℕ) : n * (6 * k - 2 * n) = 6 * n * k - 2 * n^2 := by
  rw [pow_two]
  by_cases h : 2 * n ≤ 6 * k
  · rw [Nat.mul_sub_left_distrib]
    ring
  · have h1 : 6 * k - 2 * n = 0 := by omega
    have h2 : 6 * n * k - 2 * (n * n) = 0 := by omega
    rw [h1, h2, mul_zero]

