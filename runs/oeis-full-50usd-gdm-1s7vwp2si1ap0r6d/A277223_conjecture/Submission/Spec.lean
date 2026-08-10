import FormalConjectures.Util.ProblemImports

open Nat Set

/-- The sum of the decimal digits of a natural number $m$. -/
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/--
A277223: $a(n)$ is the largest multiplier $k$ such that $m = k \cdot n$ is $n$ times the sum of its decimal digits.
This is equivalent to $a(n) = \max \{ k \in \mathbb{N} \mid k = \text{sum\_digits}_{10}(k \cdot n) \}$.
-/
noncomputable def A277223 (n : ℕ) : ℕ :=
  -- Define the set of all $k \in \mathbb{N}$ satisfying the property.
  -- This set is bounded and non-empty (contains 0), so its supremum is the maximum element.
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }

  -- sSup (supremum) in the complete lattice $\mathbb{N}$ gives the maximum element.
  sSup valid_multipliers

lemma sum_digits_eq_zero (m : ℕ) (h : sum_digits_10 m = 0) : m = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · exact hm
    · have h_sum : sum_digits_10 m = m % 10 + sum_digits_10 (m / 10) := by
        change (digits 10 m).sum = m % 10 + (digits 10 (m / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hm10 : m / 10 < m := by omega
      have hm_div := ih (m / 10) hm10 (by omega)
      omega

lemma sum_digits_10_9 : sum_digits_10 9 = 9 := by
  change (digits 10 9).sum = 9
  rw [digits_of_lt 10 9 (by decide) (by decide)]
  rfl

lemma sum_digits_10_mul_10 (m : ℕ) : sum_digits_10 (10 * m) = sum_digits_10 m := by
  by_cases h : m = 0
  · subst h; simp [sum_digits_10, digits_zero]
  · change (digits 10 (10 * m)).sum = (digits 10 m).sum
    rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
    have h1 : (10 * m) % 10 = 0 := by omega
    have h2 : (10 * m) / 10 = m := by omega
    rw [h1, h2]
    simp

lemma sum_digits_one (n : ℕ) (h : sum_digits_10 n = 1) : sum_digits_10 (9 * n) = 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 1 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_9]
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 9 * n = 10 * (9 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_10_18 : sum_digits_10 18 = 9 := by
  change (digits 10 18).sum = 9
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_two (n : ℕ) (h : sum_digits_10 n = 2) :
  sum_digits_10 (9 * n) = 9 ∨ sum_digits_10 (9 * n) = 18 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 2 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 1) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 2) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 2 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_18]
      · have hn_div_lt : n / 10 < n := by omega
        have h_9_div := sum_digits_one (n / 10) h2
        have h_9n : 9 * n = 9 + 10 * (9 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (9 * n) = 9 + sum_digits_10 (9 * (n / 10)) := by
          change (digits 10 (9 * n)).sum = 9 + (digits 10 (9 * (n / 10))).sum
          rw [h_9n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (9 + 10 * (9 * (n / 10))) % 10 = 9 := by omega
            have h_div : (9 + 10 * (9 * (n / 10))) / 10 = 9 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_9_div]
        right
        rfl
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 9 * n = 10 * (9 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1


lemma sum_digits_10_3 : sum_digits_10 3 = 3 := by
  change (digits 10 3).sum = 3
  rw [digits_of_lt 10 3 (by decide) (by decide)]
  rfl

lemma sum_digits_10_6 : sum_digits_10 6 = 6 := by
  change (digits 10 6).sum = 6
  rw [digits_of_lt 10 6 (by decide) (by decide)]
  rfl

lemma sum_digits_three_mul (n : ℕ) (h : sum_digits_10 n = 1) : sum_digits_10 (3 * n) = 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 1 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_3]
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 3 * n = 10 * (3 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_six_mul (n : ℕ) (h : sum_digits_10 n = 2) : sum_digits_10 (3 * n) = 6 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 2 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 1) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 2) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 2 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_6]
      · have hn_div_lt : n / 10 < n := by omega
        have h_3_div := sum_digits_three_mul (n / 10) h2
        have h_3n : 3 * n = 3 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 3 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 3 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (3 + 10 * (3 * (n / 10))) % 10 = 3 := by omega
            have h_div : (3 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 3 * n = 10 * (3 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_three (n : ℕ) (h : sum_digits_10 n = 3) : sum_digits_10 (3 * n) = 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 3 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 2 ∧ sum_digits_10 (n / 10) = 1) ∨
                     (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 2) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 3) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 3 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_9]
      · have hn_div_lt : n / 10 < n := by omega
        have h_3_div := sum_digits_three_mul (n / 10) h2
        have h_3n : 3 * n = 6 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 6 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 6 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (6 + 10 * (3 * (n / 10))) % 10 = 6 := by omega
            have h_div : (6 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        have h_3_div := sum_digits_six_mul (n / 10) h2
        have h_3n : 3 * n = 3 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 3 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 3 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (3 + 10 * (3 * (n / 10))) % 10 = 3 := by omega
            have h_div : (3 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 3 * n = 10 * (3 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_lt_ten (n : ℕ) (hn : n ≥ 10) : sum_digits_10 n < n := by
  have h_div : n / 10 ≠ 0 := by omega
  have h_sum : (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum := by
    rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
    rfl
  have h_le := digit_sum_le 10 (n / 10)
  have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
  change (digits 10 n).sum < n
  rw [h_sum]
  omega


lemma sum_digits_le (n : ℕ) : sum_digits_10 n ≤ n := by
  by_cases hn : n ≥ 10
  · have := sum_digits_lt_ten n hn
    omega
  · by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero]
    · have : sum_digits_10 n = n := by
        change (digits 10 n).sum = n
        have h_lt : n < 10 := by omega
        rw [digits_of_lt 10 n hn0 h_lt]
        rfl
      omega

lemma sum_digits_mod_9 (m : ℕ) : sum_digits_10 m ≡ m [MOD 9] := by
  exact (modEq_digits_sum 9 10 (by rfl) m).symm

lemma k_notin_valid_multipliers (n k : ℕ) (hn3 : n % 3 ≠ 1)
  (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ k = 11) :
  k ≠ sum_digits_10 (k * n) := by
  intro h
  have h1 := sum_digits_mod_9 (k * n)
  rw [← h] at h1
  have h2 : k % 9 = (k * n) % 9 := h1
  have hn_mod : n % 9 < 9 := Nat.mod_lt _ (by decide)
  have hn3_9 : n % 9 ≠ 1 ∧ n % 9 ≠ 4 ∧ n % 9 ≠ 7 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega


lemma k_notin_valid_multipliers_9 (n k : ℕ) (hn9 : n % 9 ≠ 1)
  (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ k = 11) :
  k ≠ sum_digits_10 (k * n) := by
  intro h
  have h1 := sum_digits_mod_9 (k * n)
  rw [← h] at h1
  have h2 : k % 9 = (k * n) % 9 := h1
  have hn_mod : n % 9 < 9 := Nat.mod_lt _ (by decide)
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega


lemma k_mod_3 (n K : ℕ) (hn : n % 9 ≠ 1) (h : K = sum_digits_10 (K * n)) : 3 ∣ K := by
  have h1 := sum_digits_mod_9 (K * n)
  rw [← h] at h1
  have h2 : K % 9 = (K * n) % 9 := h1
  have hn_mod : n % 9 < 9 := Nat.mod_lt _ (by decide)
  have hK_mod : K % 9 < 9 := Nat.mod_lt _ (by decide)
  have h_mul : (K * n) % 9 = (K % 9 * (n % 9)) % 9 := Nat.mul_mod K n 9
  rw [h_mul] at h2
  generalize hk9 : K % 9 = k9 at *
  generalize hn9 : n % 9 = n9 at *
  have h_div : 3 ∣ K ↔ 3 ∣ k9 := by
    have : K = k9 + 9 * (K / 9) := by
      have h_eq : K = K % 9 + 9 * (K / 9) := (Nat.mod_add_div K 9).symm
      omega
    omega
  rw [h_div]
  have h_cases : n9 = 1 ∨ 3 ∣ k9 := by
    interval_cases k9 <;> interval_cases n9
    all_goals revert h2
    all_goals decide
  rcases h_cases with h_cases | h_cases
  · exfalso; exact hn h_cases
  · exact h_cases


lemma sum_digits_10_11 : sum_digits_10 11 = 2 := by
  change (digits 10 11).sum = 2
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_13 : sum_digits_10 13 = 4 := by
  change (digits 10 13).sum = 4
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_15 : sum_digits_10 15 = 6 := by
  change (digits 10 15).sum = 6
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_17 : sum_digits_10 17 = 8 := by
  change (digits 10 17).sum = 8
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_19 : sum_digits_10 19 = 10 := by
  change (digits 10 19).sum = 10
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_99 : sum_digits_10 99 = 18 := by
  change (digits 10 99).sum = 18
  rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
  rw [digits_of_lt 10 9 (by decide) (by decide)]
  rfl

lemma sum_digits_10_1 : sum_digits_10 1 = 1 := by
  change (digits 10 1).sum = 1
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl

lemma sum_digits_10_5 : sum_digits_10 5 = 5 := by
  change (digits 10 5).sum = 5
  rw [digits_of_lt 10 5 (by decide) (by decide)]
  rfl

lemma sum_digits_10_7 : sum_digits_10 7 = 7 := by
  change (digits 10 7).sum = 7
  rw [digits_of_lt 10 7 (by decide) (by decide)]
  rfl

lemma sum_digits_eleven_mul (n : ℕ) (h : sum_digits_10 n = 1) : sum_digits_10 (11 * n) = 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have hn10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero (n / 10) h2
        have hn_val : n = 1 := by
          have h_eq : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        simp [sum_digits_10_11]
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 11 * n = 10 * (11 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_three_plus_one (q : ℕ) (hq : sum_digits_10 q = 1) : sum_digits_10 (3 * q + 1) = 4 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at hq
    · have h_sum : sum_digits_10 q = q % 10 + sum_digits_10 (q / 10) := by
        change (digits 10 q).sum = q % 10 + (digits 10 (q / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hq
      have h_cases : (q % 10 = 1 ∧ sum_digits_10 (q / 10) = 0) ∨
                     (q % 10 = 0 ∧ sum_digits_10 (q / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hq_div : q / 10 = 0 := sum_digits_eq_zero _ h2
        have hq_val : q = 1 := by
          have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
          omega
        subst hq_val
        change (digits 10 4).sum = 4
        rw [digits_of_lt 10 4 (by decide) (by decide)]
        rfl
      · have hq_div_lt : q / 10 < q := by omega
        have ih1 := ih (q / 10) hq_div_lt h2
        have h_3q : 3 * q + 1 = 1 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q + 1) = 1 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q + 1)).sum = 1 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (1 + 10 * (3 * (q / 10))) % 10 = 1 := by omega
            have h_div : (1 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2]
        have h_3_div := sum_digits_three_mul (q / 10) h2
        omega

lemma sum_digits_three_plus_one_two (q : ℕ) (hq : sum_digits_10 q = 2) :
  sum_digits_10 (3 * q + 1) = 7 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at hq
    · have h_sum : sum_digits_10 q = q % 10 + sum_digits_10 (q / 10) := by
        change (digits 10 q).sum = q % 10 + (digits 10 (q / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hq
      have h_cases : (q % 10 = 2 ∧ sum_digits_10 (q / 10) = 0) ∨
                     (q % 10 = 1 ∧ sum_digits_10 (q / 10) = 1) ∨
                     (q % 10 = 0 ∧ sum_digits_10 (q / 10) = 2) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hq_div : q / 10 = 0 := sum_digits_eq_zero _ h2
        have hq_val : q = 2 := by
          have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
          omega
        subst hq_val
        change (digits 10 7).sum = 7
        rw [digits_of_lt 10 7 (by decide) (by decide)]
        rfl
      · have hq_div_lt : q / 10 < q := by omega
        have h_3_div := sum_digits_three_mul (q / 10) h2
        have h_3q : 3 * q + 1 = 4 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q + 1) = 4 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q + 1)).sum = 4 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (4 + 10 * (3 * (q / 10))) % 10 = 4 := by omega
            have h_div : (4 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        have ih1 := ih (q / 10) hq_div_lt h2
        have h_3q : 3 * q + 1 = 10 * (3 * (q / 10)) + 1 := by omega
        have h_sum2 : sum_digits_10 (3 * q + 1) = 1 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q + 1)).sum = 1 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (3 * (q / 10)) + 1) % 10 = 1 := by omega
            have h_div : (10 * (3 * (q / 10)) + 1) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2]
        have h_3_div := sum_digits_six_mul (q / 10) h2
        omega


lemma sum_digits_four_mul (q : ℕ) (hq : sum_digits_10 q = 4) :
  sum_digits_10 (3 * q) = 3 ∨ sum_digits_10 (3 * q) = 12 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at hq
    · have h_sum : sum_digits_10 q = q % 10 + sum_digits_10 (q / 10) := by
        change (digits 10 q).sum = q % 10 + (digits 10 (q / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hq
      have h_cases : (q % 10 = 4 ∧ sum_digits_10 (q / 10) = 0) ∨
                     (q % 10 = 3 ∧ sum_digits_10 (q / 10) = 1) ∨
                     (q % 10 = 2 ∧ sum_digits_10 (q / 10) = 2) ∨
                     (q % 10 = 1 ∧ sum_digits_10 (q / 10) = 3) ∨
                     (q % 10 = 0 ∧ sum_digits_10 (q / 10) = 4) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hq_div : q / 10 = 0 := sum_digits_eq_zero _ h2
        have hq_val : q = 4 := by
          have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
          omega
        subst hq_val
        left
        change (digits 10 12).sum = 3
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 1 (by decide) (by decide)]
        rfl
      · have hq_div_lt : q / 10 < q := by omega
        right
        have h_3_div := sum_digits_three_mul (q / 10) h2
        have h_3q : 3 * q = 9 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 9 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 9 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (9 + 10 * (3 * (q / 10))) % 10 = 9 := by omega
            have h_div : (9 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        right
        have h_3_div := sum_digits_six_mul (q / 10) h2
        have h_3q : 3 * q = 6 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 6 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 6 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (6 + 10 * (3 * (q / 10))) % 10 = 6 := by omega
            have h_div : (6 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        right
        have h_3_div := sum_digits_three (q / 10) h2
        have h_3q : 3 * q = 3 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 3 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 3 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (3 + 10 * (3 * (q / 10))) % 10 = 3 := by omega
            have h_div : (3 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        have ih1 := ih (q / 10) hq_div_lt h2
        have h_mul_eq : 3 * q = 10 * (3 * (q / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_five_mul (q : ℕ) (hq : sum_digits_10 q = 5) :
  sum_digits_10 (3 * q) = 6 ∨ sum_digits_10 (3 * q) = 15 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at hq
    · have h_sum : sum_digits_10 q = q % 10 + sum_digits_10 (q / 10) := by
        change (digits 10 q).sum = q % 10 + (digits 10 (q / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hq
      have h_cases : (q % 10 = 5 ∧ sum_digits_10 (q / 10) = 0) ∨
                     (q % 10 = 4 ∧ sum_digits_10 (q / 10) = 1) ∨
                     (q % 10 = 3 ∧ sum_digits_10 (q / 10) = 2) ∨
                     (q % 10 = 2 ∧ sum_digits_10 (q / 10) = 3) ∨
                     (q % 10 = 1 ∧ sum_digits_10 (q / 10) = 4) ∨
                     (q % 10 = 0 ∧ sum_digits_10 (q / 10) = 5) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hq_div : q / 10 = 0 := sum_digits_eq_zero _ h2
        have hq_val : q = 5 := by
          have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
          omega
        subst hq_val
        left
        exact sum_digits_10_15
      · have hq_div_lt : q / 10 < q := by omega
        left
        have h_3_div := sum_digits_three_plus_one (q / 10) h2
        have h_3q : 3 * q = 2 + 10 * (3 * (q / 10) + 1) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 2 + sum_digits_10 (3 * (q / 10) + 1) := by
          change (digits 10 (3 * q)).sum = 2 + (digits 10 (3 * (q / 10) + 1)).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (2 + 10 * (3 * (q / 10) + 1)) % 10 = 2 := by omega
            have h_div : (2 + 10 * (3 * (q / 10) + 1)) / 10 = 3 * (q / 10) + 1 := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        right
        have h_3_div := sum_digits_six_mul (q / 10) h2
        have h_3q : 3 * q = 9 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 9 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 9 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (9 + 10 * (3 * (q / 10))) % 10 = 9 := by omega
            have h_div : (9 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        right
        have h_3_div := sum_digits_three (q / 10) h2
        have h_3q : 3 * q = 6 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 6 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 6 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (6 + 10 * (3 * (q / 10))) % 10 = 6 := by omega
            have h_div : (6 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hq_div_lt : q / 10 < q := by omega
        have h_3_div := sum_digits_four_mul (q / 10) h2
        have h_3q : 3 * q = 3 + 10 * (3 * (q / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * q) = 3 + sum_digits_10 (3 * (q / 10)) := by
          change (digits 10 (3 * q)).sum = 3 + (digits 10 (3 * (q / 10))).sum
          rw [h_3q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (3 + 10 * (3 * (q / 10))) % 10 = 3 := by omega
            have h_div : (3 + 10 * (3 * (q / 10))) / 10 = 3 * (q / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2]
        rcases h_3_div with hd3 | hd12
        · left; omega
        · right; omega
      · have hq_div_lt : q / 10 < q := by omega
        have ih1 := ih (q / 10) hq_div_lt h2
        have h_mul_eq : 3 * q = 10 * (3 * (q / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_six (n : ℕ) (h : sum_digits_10 n = 6) :
  sum_digits_10 (3 * n) = 9 ∨ sum_digits_10 (3 * n) = 18 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h
    · have h_sum : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
        change (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h
      have h_cases : (n % 10 = 6 ∧ sum_digits_10 (n / 10) = 0) ∨
                     (n % 10 = 5 ∧ sum_digits_10 (n / 10) = 1) ∨
                     (n % 10 = 4 ∧ sum_digits_10 (n / 10) = 2) ∨
                     (n % 10 = 3 ∧ sum_digits_10 (n / 10) = 3) ∨
                     (n % 10 = 2 ∧ sum_digits_10 (n / 10) = 4) ∨
                     (n % 10 = 1 ∧ sum_digits_10 (n / 10) = 5) ∨
                     (n % 10 = 0 ∧ sum_digits_10 (n / 10) = 6) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn_div : n / 10 = 0 := sum_digits_eq_zero _ h2
        have hn_val : n = 6 := by
          have : n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm
          omega
        subst hn_val
        left
        exact sum_digits_10_18
      · have hn_div_lt : n / 10 < n := by omega
        left
        have h_3_div := sum_digits_three_plus_one (n / 10) h2
        have h_3n : 3 * n = 5 + 10 * (3 * (n / 10) + 1) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 5 + sum_digits_10 (3 * (n / 10) + 1) := by
          change (digits 10 (3 * n)).sum = 5 + (digits 10 (3 * (n / 10) + 1)).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (5 + 10 * (3 * (n / 10) + 1)) % 10 = 5 := by omega
            have h_div : (5 + 10 * (3 * (n / 10) + 1)) / 10 = 3 * (n / 10) + 1 := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        left
        have h_3_div := sum_digits_three_plus_one_two (n / 10) h2
        have h_3n : 3 * n = 2 + 10 * (3 * (n / 10) + 1) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 2 + sum_digits_10 (3 * (n / 10) + 1) := by
          change (digits 10 (3 * n)).sum = 2 + (digits 10 (3 * (n / 10) + 1)).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (2 + 10 * (3 * (n / 10) + 1)) % 10 = 2 := by omega
            have h_div : (2 + 10 * (3 * (n / 10) + 1)) / 10 = 3 * (n / 10) + 1 := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        right
        have h_3_div := sum_digits_three (n / 10) h2
        have h_3n : 3 * n = 9 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 9 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 9 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (9 + 10 * (3 * (n / 10))) % 10 = 9 := by omega
            have h_div : (9 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2, h_3_div]
      · have hn_div_lt : n / 10 < n := by omega
        have h_3_div := sum_digits_four_mul (n / 10) h2
        have h_3n : 3 * n = 6 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 6 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 6 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (6 + 10 * (3 * (n / 10))) % 10 = 6 := by omega
            have h_div : (6 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2]
        rcases h_3_div with hd3 | hd12
        · left; omega
        · right; omega
      · have hn_div_lt : n / 10 < n := by omega
        have h_3_div := sum_digits_five_mul (n / 10) h2
        have h_3n : 3 * n = 3 + 10 * (3 * (n / 10)) := by omega
        have h_sum2 : sum_digits_10 (3 * n) = 3 + sum_digits_10 (3 * (n / 10)) := by
          change (digits 10 (3 * n)).sum = 3 + (digits 10 (3 * (n / 10))).sum
          rw [h_3n]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (3 + 10 * (3 * (n / 10))) % 10 = 3 := by omega
            have h_div : (3 + 10 * (3 * (n / 10))) / 10 = 3 * (n / 10) := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum2]
        rcases h_3_div with hd6 | hd15
        · left; omega
        · right; omega
      · have hn_div_lt : n / 10 < n := by omega
        have ih1 := ih (n / 10) hn_div_lt h2
        have h_mul_eq : 3 * n = 10 * (3 * (n / 10)) := by omega
        rw [h_mul_eq, sum_digits_10_mul_10]
        exact ih1



lemma sum_digits_odd_one (m : ℕ) (h : sum_digits_10 (2 * m + 1) = 1) : m = 0 := by
  by_cases hm : m = 0
  · exact hm
  · have h_sum : sum_digits_10 (2 * m + 1) = (2 * m + 1) % 10 + sum_digits_10 ((2 * m + 1) / 10) := by
      change (digits 10 (2 * m + 1)).sum = (2 * m + 1) % 10 + (digits 10 ((2 * m + 1) / 10)).sum
      rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
      rfl
    rw [h_sum] at h
    have h_cases : (2 * m + 1) % 10 = 1 ∧ sum_digits_10 ((2 * m + 1) / 10) = 0 := by omega
    rcases h_cases with ⟨h1, h2⟩
    have h_div_zero : (2 * m + 1) / 10 = 0 := sum_digits_eq_zero _ h2
    have hm_lt : m < 5 := by omega
    have h_contra : False := by
      interval_cases m
      · omega
      · omega
      · omega
      · omega
      · omega
    exfalso; exact h_contra

lemma sum_digits_odd_18 (q : ℕ) (h : sum_digits_10 (2 * q + 1) = 2) :
  sum_digits_10 (18 * q + 9) = 18 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10] at h
    · by_cases hq_div : q / 10 = 0
      · have hq_lt : q < 10 := by omega
        interval_cases q
        · omega
        · exfalso; revert h; rw [sum_digits_10_3]; decide
        · exfalso; revert h; rw [sum_digits_10_5]; decide
        · exfalso; revert h; rw [sum_digits_10_7]; decide
        · exfalso; revert h; rw [sum_digits_10_9]; decide
        · rw [sum_digits_10_99]
        · exfalso; revert h; rw [sum_digits_10_13]; decide
        · exfalso; revert h; rw [sum_digits_10_15]; decide
        · exfalso; revert h; rw [sum_digits_10_17]; decide
        · exfalso; revert h; rw [sum_digits_10_19]; decide
      · have h_sum : sum_digits_10 (2 * q + 1) = (2 * q + 1) % 10 + sum_digits_10 ((2 * q + 1) / 10) := by
          change (digits 10 (2 * q + 1)).sum = (2 * q + 1) % 10 + (digits 10 ((2 * q + 1) / 10)).sum
          rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
          rfl
        rw [h_sum] at h
        have hq_cases : q % 10 < 5 ∨ q % 10 ≥ 5 := by omega
        rcases hq_cases with h_lt | h_ge
        · have h_cases : ((2 * q + 1) % 10 = 1 ∧ sum_digits_10 ((2 * q + 1) / 10) = 1) := by omega
          rcases h_cases with ⟨h1, h2⟩
          have h_div_eq : (2 * q + 1) / 10 = 2 * (q / 10) := by
            have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
            omega
          rw [h_div_eq] at h2
          have h18_div : sum_digits_10 (18 * (q / 10)) = 9 := by
            have := sum_digits_one (2 * (q / 10)) h2
            have h_mul_eq : 9 * (2 * (q / 10)) = 18 * (q / 10) := by omega
            rw [h_mul_eq] at this
            exact this
          have h_q_mod10 : q % 10 = 0 := by
            have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
            omega
          have h_div_eq2 : q / 10 < q := by omega
          have h_18q : 18 * q + 9 = 10 * (18 * (q / 10)) + 9 := by omega
          change (digits 10 (18 * q + 9)).sum = 18
          rw [h_18q]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (18 * (q / 10)) + 9) % 10 = 9 := by omega
            have h_div : (10 * (18 * (q / 10)) + 9) / 10 = 18 * (q / 10) := by omega
            rw [h_mod, h_div]
            change (digits 10 (18 * (q / 10))).sum = 9 at h18_div
            simp
            omega
          · omega
        · have h_div_eq : (2 * q + 1) / 10 = 2 * (q / 10) + 1 := by
            have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
            omega
          rw [h_div_eq] at h
          have h_cases : ((2 * q + 1) % 10 = 1 ∧ sum_digits_10 (2 * (q / 10) + 1) = 1) := by omega
          rcases h_cases with ⟨h1, h2⟩
          have h_q_div2 : q / 10 = 0 := sum_digits_odd_one (q / 10) h2
          omega


lemma sum_digits_two_cases (n : ℕ) (h2 : sum_digits_10 (2 * n) = 2) :
  sum_digits_10 (18 * n) = 18 ∨ sum_digits_10 (9 * n) = 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h2
    · have h_sum : sum_digits_10 (2 * n) = (2 * n) % 10 + sum_digits_10 ((2 * n) / 10) := by
        change (digits 10 (2 * n)).sum = (2 * n) % 10 + (digits 10 ((2 * n) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at h2
      have hn10 : (2 * n) % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : ((2 * n) % 10 = 2 ∧ sum_digits_10 ((2 * n) / 10) = 0) ∨
                     ((2 * n) % 10 = 1 ∧ sum_digits_10 ((2 * n) / 10) = 1) ∨
                     ((2 * n) % 10 = 0 ∧ sum_digits_10 ((2 * n) / 10) = 2) := by omega
      rcases h_cases with ⟨h1, h2_div⟩ | ⟨h1, h2_div⟩ | ⟨h1, h2_div⟩
      · have hn_div : (2 * n) / 10 = 0 := sum_digits_eq_zero _ h2_div
        have hn_val : n = 1 := by omega
        subst hn_val
        right
        simp [sum_digits_10_9]
      · -- (2*n) % 10 = 1 is impossible for even numbers!
        omega
      · have hn_div_lt : n / 10 < n := by omega
        have hn_mod10 : n % 10 = 0 ∨ n % 10 = 5 := by omega
        rcases hn_mod10 with hr0 | hr5
        · have h_div_eq : (2 * n) / 10 = 2 * (n / 10) := by omega
          rw [h_div_eq] at h2_div
          have ih1 := ih (n / 10) hn_div_lt h2_div
          rcases ih1 with ih1 | ih1
          · left
            have h_18n : 18 * n = 10 * (18 * (n / 10)) := by omega
            rw [h_18n, sum_digits_10_mul_10]
            exact ih1
          · right
            have h_9n : 9 * n = 10 * (9 * (n / 10)) := by omega
            rw [h_9n, sum_digits_10_mul_10]
            exact ih1
        · left
          -- n % 10 = 5, so n = 10 * (n/10) + 5
          have h_18n : 18 * n = 10 * (18 * (n / 10)) + 90 := by omega
          have h_sum18 : sum_digits_10 (18 * n) = 18 := by
            have h_sum18' : sum_digits_10 (18 * n) = sum_digits_10 (18 * (n / 10) + 9) := by
              change (digits 10 (18 * n)).sum = (digits 10 (18 * (n / 10) + 9)).sum
              rw [h_18n]
              rw [digits_eq_cons_digits_div (b := 10) (by decide)]
              · have h_mod : (10 * (18 * (n / 10)) + 90) % 10 = 0 := by omega
                have h_div : (10 * (18 * (n / 10)) + 90) / 10 = 18 * (n / 10) + 9 := by omega
                rw [h_mod, h_div]
                simp [sum_digits_10]
              · omega
            rw [h_sum18']
            have h_div_eq : (2 * n) / 10 = 2 * (n / 10) + 1 := by omega
            rw [h_div_eq] at h2_div
            exact sum_digits_odd_18 (n / 10) h2_div
          exact h_sum18

lemma sum_digits_9n (n : ℕ) (hn : n > 0) :
  sum_digits_10 (9 * n) = 9 ∨ sum_digits_10 (9 * n) = 18 ∨ sum_digits_10 (9 * n) ≥ 27 := by
  have h_mod := sum_digits_mod_9 (9 * n)
  have h_mul_mod : (9 * n) % 9 = 0 := by omega
  have h_div : sum_digits_10 (9 * n) % 9 = 0 := by
    -- h_mod is: sum_digits_10 (9 * n) ≡ 9 * n [MOD 9]
    -- Since (9 * n) % 9 = 0, we have sum_digits_10 (9 * n) % 9 = 0
    have : sum_digits_10 (9 * n) % 9 = (9 * n) % 9 := h_mod
    omega
  have h_pos : sum_digits_10 (9 * n) > 0 := by
    by_contra h_zero
    have h_eq_zero : sum_digits_10 (9 * n) = 0 := by omega
    have h_n_zero := sum_digits_eq_zero (9 * n) h_eq_zero
    omega
  omega


lemma A277223_one : A277223 1 = 9 := by
  unfold A277223
  have h9 : 9 ∈ { k : ℕ | k = sum_digits_10 (k * 1) } := by
    simp [sum_digits_10_9]
  have h_nonempty : { k : ℕ | k = sum_digits_10 (k * 1) }.Nonempty := ⟨9, h9⟩
  have h_ub (k : ℕ) (hk : k ∈ { k : ℕ | k = sum_digits_10 (k * 1) }) : k ≤ 9 := by
    simp at hk
    by_contra h_gt
    have hk10 : k ≥ 10 := by omega
    have h_lt := sum_digits_lt_ten k hk10
    omega
  have h_bdd : BddAbove { k : ℕ | k = sum_digits_10 (k * 1) } := ⟨9, h_ub⟩
  have h_le := csSup_le h_nonempty h_ub
  have h_ge := le_csSup h_bdd h9
  exact le_antisymm h_le h_ge


lemma sum_digits_odd_four (y : ℕ) (hy : sum_digits_10 y = 4) (h_odd : y % 2 = 1) : sum_digits_10 (3 * y) = 12 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [sum_digits_10] at hy
  have h_sum : sum_digits_10 y = y % 10 + sum_digits_10 (y / 10) := by
    change (digits 10 y).sum = y % 10 + (digits 10 (y / 10)).sum
    rw [digits_eq_cons_digits_div (b := 10) (by decide) hy0]
    rfl
  rw [h_sum] at hy
  have hy10 : y % 10 < 10 := Nat.mod_lt _ (by decide)
  have hy_odd : y % 10 % 2 = 1 := by
    have : y = y % 10 + 10 * (y / 10) := (Nat.mod_add_div y 10).symm
    omega
  have h_cases : y % 10 = 1 ∨ y % 10 = 3 ∨ y % 10 = 5 ∨ y % 10 = 7 ∨ y % 10 = 9 := by omega
  rcases h_cases with h1 | h3 | h5 | h7 | h9
  · have h_div : sum_digits_10 (y / 10) = 3 := by omega
    have h_3y : 3 * y = 3 + 10 * (3 * (y / 10)) := by omega
    change (digits 10 (3 * y)).sum = 12
    rw [h_3y]
    rw [digits_eq_cons_digits_div (b := 10) (by decide)]
    · have h_mod : (3 + 10 * (3 * (y / 10))) % 10 = 3 := by omega
      have h_div_eq : (3 + 10 * (3 * (y / 10))) / 10 = 3 * (y / 10) := by omega
      rw [h_mod, h_div_eq]
      change 3 + sum_digits_10 (3 * (y / 10)) = 12
      rw [sum_digits_three (y / 10) h_div]
    · omega
  · have h_div : sum_digits_10 (y / 10) = 1 := by omega
    have h_3y : 3 * y = 9 + 10 * (3 * (y / 10)) := by omega
    change (digits 10 (3 * y)).sum = 12
    rw [h_3y]
    rw [digits_eq_cons_digits_div (b := 10) (by decide)]
    · have h_mod : (9 + 10 * (3 * (y / 10))) % 10 = 9 := by omega
      have h_div_eq : (9 + 10 * (3 * (y / 10))) / 10 = 3 * (y / 10) := by omega
      rw [h_mod, h_div_eq]
      change 9 + sum_digits_10 (3 * (y / 10)) = 12
      rw [sum_digits_three_mul (y / 10) h_div]
    · omega
  · omega
  · omega
  · omega

lemma sum_digits_four_six (q : ℕ) (h2q : sum_digits_10 (2 * q) = 4) (h6q : sum_digits_10 (6 * q) = 3) : sum_digits_10 q = 2 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at h2q
    · have h_sum2q : sum_digits_10 (2 * q) = (2 * q) % 10 + sum_digits_10 ((2 * q) / 10) := by
        change (digits 10 (2 * q)).sum = (2 * q) % 10 + (digits 10 ((2 * q) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      have h_sum6q : sum_digits_10 (6 * q) = (6 * q) % 10 + sum_digits_10 ((6 * q) / 10) := by
        change (digits 10 (6 * q)).sum = (6 * q) % 10 + (digits 10 ((6 * q) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2q] at h2q
      rw [h_sum6q] at h6q
      have h_mod2q : (2 * q) % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_mod6q : (6 * q) % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_even2q : (2 * q) % 10 % 2 = 0 := by
        have : 2 * q = (2 * q) % 10 + 10 * ((2 * q) / 10) := (Nat.mod_add_div (2 * q) 10).symm
        omega
      have h_cases2q : (2 * q) % 10 = 0 ∨ (2 * q) % 10 = 2 ∨ (2 * q) % 10 = 4 ∨ (2 * q) % 10 = 6 ∨ (2 * q) % 10 = 8 := by omega
      rcases h_cases2q with h_r0 | h_r2 | h_r4 | h_r6 | h_r8
      · -- (2 * q) % 10 = 0
        have h_div2q : sum_digits_10 ((2 * q) / 10) = 4 := by omega
        have h_modq : q % 10 = 0 ∨ q % 10 = 5 := by omega
        rcases h_modq with hq_r0 | hq_r5
        · -- q % 10 = 0
          have hq_div2 : (2 * q) / 10 = 2 * (q / 10) := by omega
          have hq_div6 : (6 * q) / 10 = 6 * (q / 10) := by omega
          have hq_mod6 : (6 * q) % 10 = 0 := by omega
          rw [hq_div2] at h_div2q
          rw [hq_div6, hq_mod6] at h6q
          have h_div6q : sum_digits_10 (6 * (q / 10)) = 3 := by omega
          have h_lt : q / 10 < q := by omega
          have ih1 := ih (q / 10) h_lt h_div2q h_div6q
          have h_q_eq : q = 10 * (q / 10) := by omega
          rw [h_q_eq, sum_digits_10_mul_10]
          exact ih1
        · -- q % 10 = 5
          have hq_div2 : (2 * q) / 10 = 2 * (q / 10) + 1 := by omega
          have hq_div6 : (6 * q) / 10 = 3 * (2 * (q / 10) + 1) := by omega
          have hq_mod6 : (6 * q) % 10 = 0 := by omega
          rw [hq_div2] at h_div2q
          rw [hq_div6, hq_mod6] at h6q
          have h_div6_3 : sum_digits_10 (3 * (2 * (q / 10) + 1)) = 3 := by omega
          have h_odd : (2 * (q / 10) + 1) % 2 = 1 := by omega
          have h_odd_four := sum_digits_odd_four (2 * (q / 10) + 1) h_div2q h_odd
          omega
      · -- (2 * q) % 10 = 2
        have h_div2q : sum_digits_10 ((2 * q) / 10) = 2 := by omega
        have h_modq : q % 10 = 1 ∨ q % 10 = 6 := by omega
        rcases h_modq with hq_r1 | hq_r6
        · -- q % 10 = 1
          have hq_mod6 : (6 * q) % 10 = 6 := by omega
          omega
        · -- q % 10 = 6
          have hq_mod6 : (6 * q) % 10 = 6 := by omega
          omega
      · -- (2 * q) % 10 = 4
        have h_div2q : sum_digits_10 ((2 * q) / 10) = 0 := by omega
        have hq_eq0 : (2 * q) / 10 = 0 := sum_digits_eq_zero _ h_div2q
        have hq_val : q = 2 := by omega
        subst hq_val
        change (digits 10 2).sum = 2
        rw [digits_of_lt 10 2 (by decide) (by decide)]
        rfl
      · -- (2 * q) % 10 = 6
        omega
      · -- (2 * q) % 10 = 8
        omega


lemma sum_digits_5q_plus_1 (q : ℕ) : sum_digits_10 (5 * q + 1) = sum_digits_10 (5 * q) + 1 := by
  by_cases hq0 : q = 0
  · subst hq0
    change (digits 10 1).sum = (digits 10 0).sum + 1
    rw [digits_of_lt 10 1 (by decide) (by decide)]
    rw [digits_zero]
    rfl
  · have h5q : 5 * q ≠ 0 := by omega
    have h5q1 : 5 * q + 1 ≠ 0 := by omega
    by_cases hq : q % 2 = 0
    · have h_mod : (5 * q) % 10 = 0 := by omega
      have h_div : (5 * q) / 10 = q / 2 := by omega
      have h_sum1 : sum_digits_10 (5 * q) = sum_digits_10 (q / 2) := by
        change (digits 10 (5 * q)).sum = (digits 10 (q / 2)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) h5q]
        rw [h_mod, h_div]
        simp
      have h_sum2 : sum_digits_10 (5 * q + 1) = sum_digits_10 (q / 2) + 1 := by
        change (digits 10 (5 * q + 1)).sum = (digits 10 (q / 2)).sum + 1
        rw [digits_eq_cons_digits_div (b := 10) (by decide) h5q1]
        have h_mod' : (5 * q + 1) % 10 = 1 := by omega
        have h_div' : (5 * q + 1) / 10 = q / 2 := by omega
        rw [h_mod', h_div']
        simp
        omega
      omega
    · have h_mod : (5 * q) % 10 = 5 := by omega
      have h_div : (5 * q) / 10 = q / 2 := by omega
      have h_sum1 : sum_digits_10 (5 * q) = sum_digits_10 (q / 2) + 5 := by
        change (digits 10 (5 * q)).sum = (digits 10 (q / 2)).sum + 5
        rw [digits_eq_cons_digits_div (b := 10) (by decide) h5q]
        rw [h_mod, h_div]
        simp
        omega
      have h_sum2 : sum_digits_10 (5 * q + 1) = sum_digits_10 (q / 2) + 6 := by
        change (digits 10 (5 * q + 1)).sum = (digits 10 (q / 2)).sum + 6
        rw [digits_eq_cons_digits_div (b := 10) (by decide) h5q1]
        have h_mod' : (5 * q + 1) % 10 = 6 := by omega
        have h_div' : (5 * q + 1) / 10 = q / 2 := by omega
        rw [h_mod', h_div']
        simp
        omega
      omega


lemma sum_digits_250_mul (p : ℕ) (hp : sum_digits_10 p = 1) : sum_digits_10 (250 * p) = 7 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst hp0; simp [sum_digits_10, digits_zero] at hp
    · have h_sum : sum_digits_10 p = p % 10 + sum_digits_10 (p / 10) := by
        change (digits 10 p).sum = p % 10 + (digits 10 (p / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hp
      have hp10 : p % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (p % 10 = 1 ∧ sum_digits_10 (p / 10) = 0) ∨
                     (p % 10 = 0 ∧ sum_digits_10 (p / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hp_div : p / 10 = 0 := sum_digits_eq_zero _ h2
        have hp_val : p = 1 := by
          have : p = p % 10 + 10 * (p / 10) := (Nat.mod_add_div p 10).symm
          omega
        subst hp_val
        change (digits 10 250).sum = 7
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 2 (by decide) (by decide)]
        rfl
      · have hp_div_lt : p / 10 < p := by omega
        have ih1 := ih (p / 10) hp_div_lt h2
        have h_250p : 250 * p = 10 * (250 * (p / 10)) := by omega
        rw [h_250p, sum_digits_10_mul_10]
        exact ih1

lemma sum_digits_250_plus_2 (p : ℕ) (hp : sum_digits_10 p = 1) : sum_digits_10 (250 * p + 2) = 9 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst hp0; simp [sum_digits_10, digits_zero] at hp
    · have h_sum : sum_digits_10 p = p % 10 + sum_digits_10 (p / 10) := by
        change (digits 10 p).sum = p % 10 + (digits 10 (p / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hp
      have hp10 : p % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (p % 10 = 1 ∧ sum_digits_10 (p / 10) = 0) ∨
                     (p % 10 = 0 ∧ sum_digits_10 (p / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hp_div : p / 10 = 0 := sum_digits_eq_zero _ h2
        have hp_val : p = 1 := by
          have : p = p % 10 + 10 * (p / 10) := (Nat.mod_add_div p 10).symm
          omega
        subst hp_val
        change (digits 10 252).sum = 9
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 2 (by decide) (by decide)]
        rfl
      · have hp_div_lt : p / 10 < p := by omega
        have h_250p : 250 * p + 2 = 10 * (250 * (p / 10)) + 2 := by omega
        have h_sum2 : sum_digits_10 (250 * p + 2) = sum_digits_10 (250 * (p / 10)) + 2 := by
          change (digits 10 (250 * p + 2)).sum = (digits 10 (250 * (p / 10))).sum + 2
          rw [h_250p]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (250 * (p / 10)) + 2) % 10 = 2 := by omega
            have h_div : (10 * (250 * (p / 10)) + 2) / 10 = 250 * (p / 10) := by omega
            rw [h_mod, h_div]
            generalize (digits 10 (250 * (p / 10))).sum = s
            change 2 + s = s + 2
            omega
          · omega
        rw [h_sum2]
        have h_250_mul := sum_digits_250_mul (p / 10) h2
        omega

lemma sum_digits_250_plus_26 (p : ℕ) (hp : sum_digits_10 p = 1) : sum_digits_10 (250 * p + 26) = 15 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst hp0; simp [sum_digits_10, digits_zero] at hp
    · have h_sum : sum_digits_10 p = p % 10 + sum_digits_10 (p / 10) := by
        change (digits 10 p).sum = p % 10 + (digits 10 (p / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hp
      have hp10 : p % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (p % 10 = 1 ∧ sum_digits_10 (p / 10) = 0) ∨
                     (p % 10 = 0 ∧ sum_digits_10 (p / 10) = 1) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hp_div : p / 10 = 0 := sum_digits_eq_zero _ h2
        have hp_val : p = 1 := by
          have : p = p % 10 + 10 * (p / 10) := (Nat.mod_add_div p 10).symm
          omega
        subst hp_val
        change (digits 10 276).sum = 15
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 2 (by decide) (by decide)]
        rfl
      · have hp_div_lt : p / 10 < p := by omega
        have h_250p : 250 * p + 26 = 10 * (250 * (p / 10) + 2) + 6 := by omega
        have h_sum2 : sum_digits_10 (250 * p + 26) = sum_digits_10 (250 * (p / 10) + 2) + 6 := by
          change (digits 10 (250 * p + 26)).sum = (digits 10 (250 * (p / 10) + 2)).sum + 6
          rw [h_250p]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (250 * (p / 10) + 2) + 6) % 10 = 6 := by omega
            have h_div : (10 * (250 * (p / 10) + 2) + 6) / 10 = 250 * (p / 10) + 2 := by omega
            rw [h_mod, h_div]
            generalize (digits 10 (250 * (p / 10) + 2)).sum = s
            change 6 + s = s + 6
            omega
          · omega
        rw [h_sum2]
        have h_250_plus_2 := sum_digits_250_plus_2 (p / 10) h2
        omega

lemma sum_digits_25_plus_one (x : ℕ) : sum_digits_10 (25 * x + 1) = sum_digits_10 (25 * x) + 1 := by
  by_cases hx : x % 2 = 0
  · have h_mod : (25 * x) % 10 = 0 := by omega
    have h_25x : 25 * x ≠ 0 ∨ 25 * x = 0 := by omega
    rcases h_25x with h_25x | h_25x
    · have h_sum : sum_digits_10 (25 * x + 1) = (25 * x + 1) % 10 + sum_digits_10 ((25 * x + 1) / 10) := by
        change (digits 10 (25 * x + 1)).sum = (25 * x + 1) % 10 + (digits 10 ((25 * x + 1) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      have h_sum0 : sum_digits_10 (25 * x) = (25 * x) % 10 + sum_digits_10 ((25 * x) / 10) := by
        change (digits 10 (25 * x)).sum = (25 * x) % 10 + (digits 10 ((25 * x) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) h_25x]
        rfl
      have h_mod' : (25 * x + 1) % 10 = 1 := by omega
      have h_div' : (25 * x + 1) / 10 = (25 * x) / 10 := by omega
      rw [h_sum, h_sum0, h_mod, h_mod', h_div']
      omega
    · have hx0 : x = 0 := by omega
      subst hx0
      change (digits 10 1).sum = (digits 10 0).sum + 1
      rw [digits_of_lt 10 1 (by decide) (by decide)]
      simp [digits_zero]
  · have h_mod : (25 * x) % 10 = 5 := by omega
    have h_25x : 25 * x ≠ 0 := by omega
    have h_sum : sum_digits_10 (25 * x + 1) = (25 * x + 1) % 10 + sum_digits_10 ((25 * x + 1) / 10) := by
      change (digits 10 (25 * x + 1)).sum = (25 * x + 1) % 10 + (digits 10 ((25 * x + 1) / 10)).sum
      rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
      rfl
    have h_sum0 : sum_digits_10 (25 * x) = (25 * x) % 10 + sum_digits_10 ((25 * x) / 10) := by
      change (digits 10 (25 * x)).sum = (25 * x) % 10 + (digits 10 ((25 * x) / 10)).sum
      rw [digits_eq_cons_digits_div (b := 10) (by decide) h_25x]
      rfl
    have h_mod' : (25 * x + 1) % 10 = 6 := by omega
    have h_div' : (25 * x + 1) / 10 = (25 * x) / 10 := by omega
    rw [h_sum, h_sum0, h_mod, h_mod', h_div']
    omega

lemma sum_digits_15_25_of_two (q : ℕ) (hq : sum_digits_10 q = 2) :
  sum_digits_10 (15 * q) = 3 ∨ sum_digits_10 (25 * q + 1) = 15 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at hq
    · have h_sum : sum_digits_10 q = q % 10 + sum_digits_10 (q / 10) := by
        change (digits 10 q).sum = q % 10 + (digits 10 (q / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum] at hq
      have hq10 : q % 10 < 10 := Nat.mod_lt _ (by decide)
      have h_cases : (q % 10 = 2 ∧ sum_digits_10 (q / 10) = 0) ∨
                     (q % 10 = 1 ∧ sum_digits_10 (q / 10) = 1) ∨
                     (q % 10 = 0 ∧ sum_digits_10 (q / 10) = 2) := by omega
      rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hq_div : q / 10 = 0 := sum_digits_eq_zero _ h2
        have hq_val : q = 2 := by
          have : q = q % 10 + 10 * (q / 10) := (Nat.mod_add_div q 10).symm
          omega
        subst hq_val
        left
        change (digits 10 30).sum = 3
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 3 (by decide) (by decide)]
        rfl
      · right
        have hq_div_lt : q / 10 < q := by omega
        have h_25q : 25 * q + 1 = 10 * (25 * (q / 10)) + 26 := by omega
        rw [h_25q]
        have h_eq : 10 * (25 * (q / 10)) + 26 = 250 * (q / 10) + 26 := by ring
        rw [h_eq]
        exact sum_digits_250_plus_26 (q / 10) h2
      · have hq_div_lt : q / 10 < q := by omega
        have ih1 := ih (q / 10) hq_div_lt h2
        have h_15q : 15 * q = 10 * (15 * (q / 10)) := by omega
        rcases ih1 with ih1 | ih1
        · left
          rw [h_15q, sum_digits_10_mul_10]
          exact ih1
        · right
          have h_25q : 25 * q + 1 = 10 * (25 * (q / 10)) + 1 := by omega
          rw [h_25q]
          have h_sum2 : sum_digits_10 (10 * (25 * (q / 10)) + 1) = sum_digits_10 (25 * (q / 10)) + 1 := by
            change (digits 10 (10 * (25 * (q / 10)) + 1)).sum = (digits 10 (25 * (q / 10))).sum + 1
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · have h_mod : (10 * (25 * (q / 10)) + 1) % 10 = 1 := by omega
              have h_div : (10 * (25 * (q / 10)) + 1) / 10 = 25 * (q / 10) := by omega
              rw [h_mod, h_div]
              generalize (digits 10 (25 * (q / 10))).sum = s
              change 1 + s = s + 1
              omega
            · omega
          rw [h_sum2]
          rw [← sum_digits_25_plus_one]
          exact ih1

lemma sum_digits_3_5_of_2y (y : ℕ) (h2y : sum_digits_10 (2 * y) = 2) :
  sum_digits_10 (3 * y) = 3 ∨ sum_digits_10 (5 * y + 1) = 15 := by
  by_cases hy0 : y = 0
  · subst hy0; simp [sum_digits_10, digits_zero] at h2y
  · have h_sum2y : sum_digits_10 (2 * y) = (2 * y) % 10 + sum_digits_10 ((2 * y) / 10) := by
      change (digits 10 (2 * y)).sum = (2 * y) % 10 + (digits 10 ((2 * y) / 10)).sum
      rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
      rfl
    rw [h_sum2y] at h2y
    have h_mod2y : (2 * y) % 10 = 0 ∨ (2 * y) % 10 = 2 ∨ (2 * y) % 10 = 4 ∨ (2 * y) % 10 = 6 ∨ (2 * y) % 10 = 8 := by omega
    rcases h_mod2y with r0 | r2 | r4 | r6 | r8
    · have h_div_sum : sum_digits_10 ((2 * y) / 10) = 2 := by omega
      have h_y_eq : y = 5 * ((2 * y) / 10) := by omega
      have h_3y_eq : 3 * y = 15 * ((2 * y) / 10) := by omega
      have h_5y_eq : 5 * y + 1 = 25 * ((2 * y) / 10) + 1 := by omega
      rw [h_3y_eq, h_5y_eq]
      exact sum_digits_15_25_of_two _ h_div_sum
    · have h_div_sum : sum_digits_10 ((2 * y) / 10) = 0 := by omega
      have h_div_zero : (2 * y) / 10 = 0 := sum_digits_eq_zero _ h_div_sum
      have h_y_val : y = 1 := by omega
      subst h_y_val
      left
      change (digits 10 3).sum = 3
      rw [digits_of_lt 10 3 (by decide) (by decide)]
      rfl
    · omega
    · omega
    · omega

lemma sum_digits_15_of_6_18_helper2 (X : ℕ) (h1 : sum_digits_10 (6 * X + 4) = 4) (h2 : sum_digits_10 (18 * X + 12) = 3) :
  sum_digits_10 (15 * X + 10) = 1 := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX0 : X = 0
    · subst hX0
      change (digits 10 10).sum = 1
      rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
      rw [digits_of_lt 10 1 (by decide) (by decide)]
      rfl
    · have h_sum1 : sum_digits_10 (6 * X + 4) = (6 * X + 4) % 10 + sum_digits_10 ((6 * X + 4) / 10) := by
        change (digits 10 (6 * X + 4)).sum = (6 * X + 4) % 10 + (digits 10 ((6 * X + 4) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum1] at h1
      have h_sum2 : sum_digits_10 (18 * X + 12) = (18 * X + 12) % 10 + sum_digits_10 ((18 * X + 12) / 10) := by
        change (digits 10 (18 * X + 12)).sum = (18 * X + 12) % 10 + (digits 10 ((18 * X + 12) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2] at h2
      have hX_mod10 : X % 10 = 0 ∨ X % 10 = 1 ∨ X % 10 = 2 ∨ X % 10 = 3 ∨ X % 10 = 4 ∨ X % 10 = 5 ∨ X % 10 = 6 ∨ X % 10 = 7 ∨ X % 10 = 8 ∨ X % 10 = 9 := by omega
      rcases hX_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · have hX_div_lt : X / 10 < X := by omega
        have h_6div : (6 * X + 4) / 10 = 6 * (X / 10) := by omega
        have h_mod6 : (6 * X + 4) % 10 = 4 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10)) = 0 := by omega
        have h_6div_zero := sum_digits_eq_zero _ h_6div_sum
        have hX_div_zero : X / 10 = 0 := by omega
        have hX_val : X = 0 := by omega
        subst hX_val
        change (digits 10 10).sum = 1
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 1 (by decide) (by decide)]
        rfl
      · have h_6div : (6 * X + 4) / 10 = 6 * (X / 10) + 1 := by omega
        have h_mod6 : (6 * X + 4) % 10 = 0 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10) + 1) = 4 := by omega
        have h_18div : (18 * X + 12) / 10 = 18 * (X / 10) + 3 := by omega
        have h_mod18 : (18 * X + 12) % 10 = 0 := by omega
        rw [h_18div, h_mod18] at h2
        have h_18div_sum : sum_digits_10 (18 * (X / 10) + 3) = 3 := by omega
        have h_odd : (6 * (X / 10) + 1) % 2 = 1 := by omega
        have h_odd_four := sum_digits_odd_four _ h_6div_sum h_odd
        have h_eq : 3 * (6 * (X / 10) + 1) = 18 * (X / 10) + 3 := by omega
        rw [h_eq] at h_odd_four
        omega
      · omega
      · omega
      · omega
      · have h_6div : (6 * X + 4) / 10 = 6 * (X / 10) + 3 := by omega
        have h_mod6 : (6 * X + 4) % 10 = 4 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10) + 3) = 0 := by omega
        have h_eq : 6 * (X / 10) + 3 = 0 := sum_digits_eq_zero _ h_6div_sum
        omega
      · have hX_div_lt : X / 10 < X := by omega
        have h_6eq : 6 * X + 4 = 10 * (6 * (X / 10) + 4) := by omega
        have h1_folded : sum_digits_10 (6 * (X / 10) + 4) = 4 := by
          have h_sum_6 : sum_digits_10 (6 * X + 4) = sum_digits_10 (6 * (X / 10) + 4) := by
            rw [h_6eq, sum_digits_10_mul_10]
          omega
        have h_18eq : 18 * X + 12 = 10 * (18 * (X / 10) + 12) := by omega
        have h2_folded : sum_digits_10 (18 * (X / 10) + 12) = 3 := by
          have h_sum_18 : sum_digits_10 (18 * X + 12) = sum_digits_10 (18 * (X / 10) + 12) := by
            rw [h_18eq, sum_digits_10_mul_10]
          omega
        have ih1 := ih (X / 10) hX_div_lt h1_folded h2_folded
        have h_15X : 15 * X + 10 = 10 * (15 * (X / 10) + 10) := by omega
        rw [h_15X, sum_digits_10_mul_10]
        exact ih1
      · omega
      · omega
      · omega

lemma sum_digits_15_of_6_18_helper (X : ℕ) (h1 : sum_digits_10 (6 * X + 5) = 5) (h2 : sum_digits_10 (18 * X + 15) = 6) :
  sum_digits_10 (15 * X + 12) = 3 := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX0 : X = 0
    · subst hX0
      change (digits 10 12).sum = 3
      rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
      rw [digits_of_lt 10 1 (by decide) (by decide)]
      rfl
    · have h_sum1 : sum_digits_10 (6 * X + 5) = (6 * X + 5) % 10 + sum_digits_10 ((6 * X + 5) / 10) := by
        change (digits 10 (6 * X + 5)).sum = (6 * X + 5) % 10 + (digits 10 ((6 * X + 5) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum1] at h1
      have h_sum2 : sum_digits_10 (18 * X + 15) = (18 * X + 15) % 10 + sum_digits_10 ((18 * X + 15) / 10) := by
        change (digits 10 (18 * X + 15)).sum = (18 * X + 15) % 10 + (digits 10 ((18 * X + 15) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2] at h2
      have hX_mod10 : X % 10 = 0 ∨ X % 10 = 1 ∨ X % 10 = 2 ∨ X % 10 = 3 ∨ X % 10 = 4 ∨ X % 10 = 5 ∨ X % 10 = 6 ∨ X % 10 = 7 ∨ X % 10 = 8 ∨ X % 10 = 9 := by omega
      rcases hX_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · have hX_div_lt : X / 10 < X := by omega
        have h_6div : (6 * X + 5) / 10 = 6 * (X / 10) := by omega
        have h_mod6 : (6 * X + 5) % 10 = 5 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10)) = 0 := by omega
        have h_6div_zero := sum_digits_eq_zero _ h_6div_sum
        have hX_div_zero : X / 10 = 0 := by omega
        have hX_val : X = 0 := by omega
        subst hX_val
        change (digits 10 12).sum = 3
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 1 (by decide) (by decide)]
        rfl
      · have h_6div : (6 * X + 5) / 10 = 6 * (X / 10) + 1 := by omega
        have h_mod6 : (6 * X + 5) % 10 = 1 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10) + 1) = 4 := by omega
        have h_18div : (18 * X + 15) / 10 = 18 * (X / 10) + 3 := by omega
        have h_mod18 : (18 * X + 15) % 10 = 3 := by omega
        rw [h_18div, h_mod18] at h2
        have h_18div_sum : sum_digits_10 (18 * (X / 10) + 3) = 3 := by omega
        have h_odd : (6 * (X / 10) + 1) % 2 = 1 := by omega
        have h_odd_four := sum_digits_odd_four _ h_6div_sum h_odd
        have h_eq : 3 * (6 * (X / 10) + 1) = 18 * (X / 10) + 3 := by omega
        rw [h_eq] at h_odd_four
        omega
      · omega
      · omega
      · omega
      · have h_6div : (6 * X + 5) / 10 = 6 * (X / 10) + 3 := by omega
        have h_mod6 : (6 * X + 5) % 10 = 5 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10) + 3) = 0 := by omega
        have h_6div_zero := sum_digits_eq_zero _ h_6div_sum
        omega
      · have hX_div_lt : X / 10 < X := by omega
        have h_6eq : 6 * X + 5 = 10 * (6 * (X / 10) + 4) + 1 := by omega
        have h1_folded : sum_digits_10 (6 * (X / 10) + 4) = 4 := by
          have h_sum_6 : sum_digits_10 (6 * X + 5) = sum_digits_10 (6 * (X / 10) + 4) + 1 := by
            change (digits 10 (6 * X + 5)).sum = (digits 10 (6 * (X / 10) + 4)).sum + 1
            rw [h_6eq]
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · have h_mod : (10 * (6 * (X / 10) + 4) + 1) % 10 = 1 := by omega
              have h_div : (10 * (6 * (X / 10) + 4) + 1) / 10 = 6 * (X / 10) + 4 := by omega
              rw [h_mod, h_div]
              generalize (digits 10 (6 * (X / 10) + 4)).sum = s
              change 1 + s = s + 1
              omega
            · omega
          omega
        have h_18eq : 18 * X + 15 = 10 * (18 * (X / 10) + 12) + 3 := by omega
        have h2_folded : sum_digits_10 (18 * (X / 10) + 12) = 3 := by
          have h_sum_18 : sum_digits_10 (18 * X + 15) = sum_digits_10 (18 * (X / 10) + 12) + 3 := by
            change (digits 10 (18 * X + 15)).sum = (digits 10 (18 * (X / 10) + 12)).sum + 3
            rw [h_18eq]
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · have h_mod : (10 * (18 * (X / 10) + 12) + 3) % 10 = 3 := by omega
              have h_div : (10 * (18 * (X / 10) + 12) + 3) / 10 = 18 * (X / 10) + 12 := by omega
              rw [h_mod, h_div]
              generalize (digits 10 (18 * (X / 10) + 12)).sum = s
              change 3 + s = s + 3
              omega
            · omega
          omega
        have ih1 := sum_digits_15_of_6_18_helper2 (X / 10) h1_folded h2_folded
        have h_15X : 15 * X + 12 = 10 * (15 * (X / 10) + 10) + 2 := by omega
        rw [h_15X]
        have h_sum3 : sum_digits_10 (10 * (15 * (X / 10) + 10) + 2) = sum_digits_10 (15 * (X / 10) + 10) + 2 := by
          change (digits 10 (10 * (15 * (X / 10) + 10) + 2)).sum = (digits 10 (15 * (X / 10) + 10)).sum + 2
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (15 * (X / 10) + 10) + 2) % 10 = 2 := by omega
            have h_div : (10 * (15 * (X / 10) + 10) + 2) / 10 = 15 * (X / 10) + 10 := by omega
            rw [h_mod, h_div]
            generalize (digits 10 (15 * (X / 10) + 10)).sum = s
            change 2 + s = s + 2
            omega
          · omega
        rw [h_sum3, ih1]
      · omega
      · omega
      · omega

lemma sum_digits_15_of_6_18 (q : ℕ) (h6 : sum_digits_10 (6 * q + 3) = 6) (h18 : sum_digits_10 (18 * q + 9) = 9) :
  sum_digits_10 (15 * q + 7) = 10 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at h6
    · have h_sum1 : sum_digits_10 (6 * q + 3) = (6 * q + 3) % 10 + sum_digits_10 ((6 * q + 3) / 10) := by
        change (digits 10 (6 * q + 3)).sum = (6 * q + 3) % 10 + (digits 10 ((6 * q + 3) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum1] at h6
      have h_sum2 : sum_digits_10 (18 * q + 9) = (18 * q + 9) % 10 + sum_digits_10 ((18 * q + 9) / 10) := by
        change (digits 10 (18 * q + 9)).sum = (18 * q + 9) % 10 + (digits 10 ((18 * q + 9) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2] at h18
      have hq_mod10 : q % 10 = 0 ∨ q % 10 = 1 ∨ q % 10 = 2 ∨ q % 10 = 3 ∨ q % 10 = 4 ∨ q % 10 = 5 ∨ q % 10 = 6 ∨ q % 10 = 7 ∨ q % 10 = 8 ∨ q % 10 = 9 := by omega
      rcases hq_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · have h_18div : (18 * q + 9) / 10 = 18 * (q / 10) := by omega
        have h_mod18 : (18 * q + 9) % 10 = 9 := by omega
        rw [h_18div, h_mod18] at h18
        have h_sum_zero : sum_digits_10 (18 * (q / 10)) = 0 := by omega
        have h_zero : 18 * (q / 10) = 0 := sum_digits_eq_zero _ h_sum_zero
        omega
      · omega
      · have h_6div : (6 * q + 3) / 10 = 6 * (q / 10) + 1 := by omega
        have h_mod6 : (6 * q + 3) % 10 = 5 := by omega
        rw [h_6div, h_mod6] at h6
        have h_6div_sum : sum_digits_10 (6 * (q / 10) + 1) = 1 := by omega
        have h_zero : sum_digits_10 (6 * (q / 10)) = 0 := by
          have h_sum_exp : sum_digits_10 (6 * (q / 10) + 1) = (6 * (q / 10) + 1) % 10 + sum_digits_10 ((6 * (q / 10) + 1) / 10) := by
            change (digits 10 (6 * (q / 10) + 1)).sum = (6 * (q / 10) + 1) % 10 + (digits 10 ((6 * (q / 10) + 1) / 10)).sum
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · rfl
            · omega
          rw [h_sum_exp] at h_6div_sum
          have h_mod : (6 * (q / 10) + 1) % 10 = 1 := by omega
          have h_div : (6 * (q / 10) + 1) / 10 = 6 * (q / 10) / 10 := by omega
          rw [h_mod, h_div] at h_6div_sum
          have h_zero' : sum_digits_10 (6 * (q / 10) / 10) = 0 := by omega
          have h_mod_zero : (6 * (q / 10)) % 10 = 0 := by omega
          have h_6 : 6 * (q / 10) ≠ 0 ∨ 6 * (q / 10) = 0 := by omega
          rcases h_6 with h_6 | h_6
          · have h_sum0 : sum_digits_10 (6 * (q / 10)) = (6 * (q / 10)) % 10 + sum_digits_10 (6 * (q / 10) / 10) := by
              change (digits 10 (6 * (q / 10))).sum = (6 * (q / 10)) % 10 + (digits 10 (6 * (q / 10) / 10)).sum
              rw [digits_eq_cons_digits_div (b := 10) (by decide) h_6]
              rfl
            rw [h_sum0, h_mod_zero, h_zero']
            rfl
          · rw [h_6]; rfl
        have h_div_zero := sum_digits_eq_zero _ h_zero
        have hq_div_zero : q / 10 = 0 := by omega
        have hq_val : q = 2 := by omega
        subst hq_val
        change (digits 10 37).sum = 10
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 3 (by decide) (by decide)]
        rfl
      · omega
      · omega
      · omega
      · omega
      · omega
      · have h_6div : (6 * q + 3) / 10 = 6 * (q / 10) + 5 := by omega
        have h_mod6 : (6 * q + 3) % 10 = 1 := by omega
        rw [h_6div, h_mod6] at h6
        have h_6div_sum : sum_digits_10 (6 * (q / 10) + 5) = 5 := by omega
        have h_18div : (18 * q + 9) / 10 = 18 * (q / 10) + 15 := by omega
        have h_mod18 : (18 * q + 9) % 10 = 3 := by omega
        rw [h_18div, h_mod18] at h18
        have h_18div_sum : sum_digits_10 (18 * (q / 10) + 15) = 6 := by omega
        have h_helper := sum_digits_15_of_6_18_helper (q / 10) h_6div_sum h_18div_sum
        have h_15q : 15 * q + 7 = 10 * (15 * (q / 10) + 12) + 7 := by omega
        rw [h_15q]
        have h_sum3 : sum_digits_10 (10 * (15 * (q / 10) + 12) + 7) = sum_digits_10 (15 * (q / 10) + 12) + 7 := by
          change (digits 10 (10 * (15 * (q / 10) + 12) + 7)).sum = (digits 10 (15 * (q / 10) + 12)).sum + 7
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (15 * (q / 10) + 12) + 7) % 10 = 7 := by omega
            have h_div : (10 * (15 * (q / 10) + 12) + 7) / 10 = 15 * (q / 10) + 12 := by omega
            rw [h_mod, h_div]
            change (7 :: digits 10 (15 * (q / 10) + 12)).sum = (digits 10 (15 * (q / 10) + 12)).sum + 7
            omega
          · omega
        rw [h_sum3, h_helper]
      · omega

lemma sum_digits_9_of_2_7_helper (X : ℕ) (h1 : sum_digits_10 (6 * X + 4) = 1) (h2 : sum_digits_10 (18 * X + 12) = 3) :
  sum_digits_10 (9 * X + 6) = 6 := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX0 : X = 0
    · subst hX0; simp [sum_digits_10, digits_zero] at h1
    · have h_sum1 : sum_digits_10 (6 * X + 4) = (6 * X + 4) % 10 + sum_digits_10 ((6 * X + 4) / 10) := by
        change (digits 10 (6 * X + 4)).sum = (6 * X + 4) % 10 + (digits 10 ((6 * X + 4) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum1] at h1
      have h_sum2 : sum_digits_10 (18 * X + 12) = (18 * X + 12) % 10 + sum_digits_10 ((18 * X + 12) / 10) := by
        change (digits 10 (18 * X + 12)).sum = (18 * X + 12) % 10 + (digits 10 ((18 * X + 12) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2] at h2
      have hX_mod10 : X % 10 = 0 ∨ X % 10 = 1 ∨ X % 10 = 2 ∨ X % 10 = 3 ∨ X % 10 = 4 ∨ X % 10 = 5 ∨ X % 10 = 6 ∨ X % 10 = 7 ∨ X % 10 = 8 ∨ X % 10 = 9 := by omega
      rcases hX_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · omega
      · have hX_div_lt : X / 10 < X := by omega
        have h_6div : (6 * X + 4) / 10 = 6 * (X / 10) + 1 := by omega
        have h_mod6 : (6 * X + 4) % 10 = 0 := by omega
        rw [h_6div, h_mod6] at h1
        have h_6div_sum : sum_digits_10 (6 * (X / 10) + 1) = 1 := by omega
        have h_zero : sum_digits_10 (6 * (X / 10)) = 0 := by
          have h_sum_exp : sum_digits_10 (6 * (X / 10) + 1) = (6 * (X / 10) + 1) % 10 + sum_digits_10 ((6 * (X / 10) + 1) / 10) := by
            change (digits 10 (6 * (X / 10) + 1)).sum = (6 * (X / 10) + 1) % 10 + (digits 10 ((6 * (X / 10) + 1) / 10)).sum
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · rfl
            · omega
          rw [h_sum_exp] at h_6div_sum
          have h_mod : (6 * (X / 10) + 1) % 10 = 1 := by omega
          have h_div : (6 * (X / 10) + 1) / 10 = 6 * (X / 10) / 10 := by omega
          rw [h_mod, h_div] at h_6div_sum
          have h_zero' : sum_digits_10 (6 * (X / 10) / 10) = 0 := by omega
          have h_mod_zero : (6 * (X / 10)) % 10 = 0 := by omega
          have h_6 : 6 * (X / 10) ≠ 0 ∨ 6 * (X / 10) = 0 := by omega
          rcases h_6 with h_6 | h_6
          · have h_sum0 : sum_digits_10 (6 * (X / 10)) = (6 * (X / 10)) % 10 + sum_digits_10 (6 * (X / 10) / 10) := by
              change (digits 10 (6 * (X / 10))).sum = (6 * (X / 10)) % 10 + (digits 10 (6 * (X / 10) / 10)).sum
              rw [digits_eq_cons_digits_div (b := 10) (by decide) h_6]
              rfl
            rw [h_sum0, h_mod_zero, h_zero']
            rfl
          · rw [h_6]; rfl
        have h_div_zero := sum_digits_eq_zero _ h_zero
        have hX_div_zero : X / 10 = 0 := by omega
        have hX_val : X = 1 := by omega
        subst hX_val
        change (digits 10 15).sum = 6
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 1 (by decide) (by decide)]
        rfl
      · omega
      · omega
      · omega
      · omega
      · have hX_div_lt : X / 10 < X := by omega
        have h_6eq : 6 * X + 4 = 10 * (6 * (X / 10) + 4) := by omega
        have h1_folded : sum_digits_10 (6 * (X / 10) + 4) = 1 := by
          have h_sum_6 : sum_digits_10 (6 * X + 4) = sum_digits_10 (6 * (X / 10) + 4) := by
            rw [h_6eq, sum_digits_10_mul_10]
          omega
        have h_18eq : 18 * X + 12 = 10 * (18 * (X / 10) + 12) := by omega
        have h2_folded : sum_digits_10 (18 * (X / 10) + 12) = 3 := by
          have h_sum_18 : sum_digits_10 (18 * X + 12) = sum_digits_10 (18 * (X / 10) + 12) := by
            rw [h_18eq, sum_digits_10_mul_10]
          omega
        have ih1 := ih (X / 10) hX_div_lt h1_folded h2_folded
        have h_9X : 9 * X + 6 = 10 * (9 * (X / 10) + 6) := by omega
        rw [h_9X, sum_digits_10_mul_10]
        exact ih1
      · omega
      · omega
      · omega

lemma sum_digits_9_of_2_7 (q : ℕ) (h2 : sum_digits_10 (6 * q + 5) = 2) (h7 : sum_digits_10 (18 * q + 16) = 7) :
  sum_digits_10 (9 * q + 8) = 8 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq0 : q = 0
    · subst hq0; simp [sum_digits_10, digits_zero] at h2
    · have h_sum1 : sum_digits_10 (6 * q + 5) = (6 * q + 5) % 10 + sum_digits_10 ((6 * q + 5) / 10) := by
        change (digits 10 (6 * q + 5)).sum = (6 * q + 5) % 10 + (digits 10 ((6 * q + 5) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum1] at h2
      have h_sum2 : sum_digits_10 (18 * q + 16) = (18 * q + 16) % 10 + sum_digits_10 ((18 * q + 16) / 10) := by
        change (digits 10 (18 * q + 16)).sum = (18 * q + 16) % 10 + (digits 10 ((18 * q + 16) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum2] at h7
      have hq_mod10 : q % 10 = 0 ∨ q % 10 = 1 ∨ q % 10 = 2 ∨ q % 10 = 3 ∨ q % 10 = 4 ∨ q % 10 = 5 ∨ q % 10 = 6 ∨ q % 10 = 7 ∨ q % 10 = 8 ∨ q % 10 = 9 := by omega
      rcases hq_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · omega
      · have hq_div_lt : q / 10 < q := by omega
        have h_6div : (6 * q + 5) / 10 = 6 * (q / 10) + 1 := by omega
        have h_mod6 : (6 * q + 5) % 10 = 1 := by omega
        rw [h_6div, h_mod6] at h2
        have h_6div_sum : sum_digits_10 (6 * (q / 10) + 1) = 1 := by omega
        have h_zero : sum_digits_10 (6 * (q / 10)) = 0 := by
          have h_sum_exp : sum_digits_10 (6 * (q / 10) + 1) = (6 * (q / 10) + 1) % 10 + sum_digits_10 ((6 * (q / 10) + 1) / 10) := by
            change (digits 10 (6 * (q / 10) + 1)).sum = (6 * (q / 10) + 1) % 10 + (digits 10 ((6 * (q / 10) + 1) / 10)).sum
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · rfl
            · omega
          rw [h_sum_exp] at h_6div_sum
          have h_mod : (6 * (q / 10) + 1) % 10 = 1 := by omega
          have h_div : (6 * (q / 10) + 1) / 10 = 6 * (q / 10) / 10 := by omega
          rw [h_mod, h_div] at h_6div_sum
          have h_zero' : sum_digits_10 (6 * (q / 10) / 10) = 0 := by omega
          have h_mod_zero : (6 * (q / 10)) % 10 = 0 := by omega
          have h_6 : 6 * (q / 10) ≠ 0 ∨ 6 * (q / 10) = 0 := by omega
          rcases h_6 with h_6 | h_6
          · have h_sum0 : sum_digits_10 (6 * (q / 10)) = (6 * (q / 10)) % 10 + sum_digits_10 (6 * (q / 10) / 10) := by
              change (digits 10 (6 * (q / 10))).sum = (6 * (q / 10)) % 10 + (digits 10 (6 * (q / 10) / 10)).sum
              rw [digits_eq_cons_digits_div (b := 10) (by decide) h_6]
              rfl
            rw [h_sum0, h_mod_zero, h_zero']
            rfl
          · rw [h_6]; rfl
        have h_div_zero := sum_digits_eq_zero _ h_zero
        have hq_div_zero : q / 10 = 0 := by omega
        have hq_val : q = 1 := by omega
        subst hq_val
        change (digits 10 17).sum = 8
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by decide)]
        rw [digits_of_lt 10 1 (by decide) (by decide)]
        rfl
      · omega
      · omega
      · omega
      · omega
      · have hq_div_lt : q / 10 < q := by omega
        have h_6eq : 6 * q + 5 = 10 * (6 * (q / 10) + 4) + 1 := by omega
        have h2_folded : sum_digits_10 (6 * (q / 10) + 4) = 1 := by
          have h_sum_6 : sum_digits_10 (6 * q + 5) = sum_digits_10 (6 * (q / 10) + 4) + 1 := by
            change (digits 10 (6 * q + 5)).sum = (digits 10 (6 * (q / 10) + 4)).sum + 1
            rw [h_6eq]
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · have h_mod : (10 * (6 * (q / 10) + 4) + 1) % 10 = 1 := by omega
              have h_div : (10 * (6 * (q / 10) + 4) + 1) / 10 = 6 * (q / 10) + 4 := by omega
              rw [h_mod, h_div]
              change (1 :: digits 10 (6 * (q / 10) + 4)).sum = (digits 10 (6 * (q / 10) + 4)).sum + 1
              omega
            · omega
          omega
        have h_18eq : 18 * q + 16 = 10 * (18 * (q / 10) + 12) + 4 := by omega
        have h7_folded : sum_digits_10 (18 * (q / 10) + 12) = 3 := by
          have h_sum_18 : sum_digits_10 (18 * q + 16) = sum_digits_10 (18 * (q / 10) + 12) + 4 := by
            change (digits 10 (18 * q + 16)).sum = (digits 10 (18 * (q / 10) + 12)).sum + 4
            rw [h_18eq]
            rw [digits_eq_cons_digits_div (b := 10) (by decide)]
            · have h_mod : (10 * (18 * (q / 10) + 12) + 4) % 10 = 4 := by omega
              have h_div : (10 * (18 * (q / 10) + 12) + 4) / 10 = 18 * (q / 10) + 12 := by omega
              rw [h_mod, h_div]
              change (4 :: digits 10 (18 * (q / 10) + 12)).sum = (digits 10 (18 * (q / 10) + 12)).sum + 4
              omega
            · omega
          omega
        have h_helper := sum_digits_9_of_2_7_helper (q / 10) h2_folded h7_folded
        have h_9q : 9 * q + 8 = 10 * (9 * (q / 10) + 6) + 2 := by omega
        rw [h_9q]
        have h_sum3 : sum_digits_10 (10 * (9 * (q / 10) + 6) + 2) = sum_digits_10 (9 * (q / 10) + 6) + 2 := by
          change (digits 10 (10 * (9 * (q / 10) + 6) + 2)).sum = (digits 10 (9 * (q / 10) + 6)).sum + 2
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (9 * (q / 10) + 6) + 2) % 10 = 2 := by omega
            have h_div : (10 * (9 * (q / 10) + 6) + 2) / 10 = 9 * (q / 10) + 6 := by omega
            rw [h_mod, h_div]
            change (2 :: digits 10 (9 * (q / 10) + 6)).sum = (digits 10 (9 * (q / 10) + 6)).sum + 2
            omega
          · omega
        rw [h_sum3, h_helper]
      · omega
      · omega
      · omega


lemma sum_digits_six_contradiction (n : ℕ) (h6 : sum_digits_10 (6 * n) = 6) (h18 : sum_digits_10 (18 * n) = 9) :
  sum_digits_10 (9 * n) = 9 ∨ sum_digits_10 (15 * n) = 15 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [sum_digits_10, digits_zero] at h6
    · have h_sum6 : sum_digits_10 (6 * n) = (6 * n) % 10 + sum_digits_10 ((6 * n) / 10) := by
        change (digits 10 (6 * n)).sum = (6 * n) % 10 + (digits 10 ((6 * n) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      have h_sum18 : sum_digits_10 (18 * n) = (18 * n) % 10 + sum_digits_10 ((18 * n) / 10) := by
        change (digits 10 (18 * n)).sum = (18 * n) % 10 + (digits 10 ((18 * n) / 10)).sum
        rw [digits_eq_cons_digits_div (b := 10) (by decide) (by omega)]
        rfl
      rw [h_sum6] at h6
      rw [h_sum18] at h18
      have hn_mod10 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by omega
      rcases hn_mod10 with r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9
      · have hn_div_lt : n / 10 < n := by omega
        have h_6div : (6 * n) / 10 = 6 * (n / 10) := by omega
        have h_18div : (18 * n) / 10 = 18 * (n / 10) := by omega
        have h_mod6 : (6 * n) % 10 = 0 := by omega
        have h_mod18 : (18 * n) % 10 = 0 := by omega
        rw [h_6div, h_mod6] at h6
        rw [h_18div, h_mod18] at h18
        simp [sum_digits_10] at h6 h18
        have ih1 := ih (n / 10) hn_div_lt h6 h18
        rcases ih1 with ih1 | ih1
        · left
          have : 9 * n = 10 * (9 * (n / 10)) := by omega
          rw [this, sum_digits_10_mul_10]
          exact ih1
        · right
          have : 15 * n = 10 * (15 * (n / 10)) := by omega
          rw [this, sum_digits_10_mul_10]
          exact ih1
      · have h_mod6 : (6 * n) % 10 = 6 := by omega
        have h_6div : (6 * n) / 10 = 6 * (n / 10) := by omega
        rw [h_mod6, h_6div] at h6
        have h_zero : sum_digits_10 (6 * (n / 10)) = 0 := by omega
        have h_6div_zero := sum_digits_eq_zero _ h_zero
        have hn_div_zero : (n / 10) = 0 := by omega
        have hn_val : n = 1 := by omega
        subst hn_val
        left
        exact sum_digits_10_9
      · have h_mod6 : (6 * n) % 10 = 2 := by omega
        have h_6div : (6 * n) / 10 = 6 * (n / 10) + 1 := by omega
        rw [h_mod6, h_6div] at h6
        have h_sum6_eq : sum_digits_10 (6 * (n / 10) + 1) = 4 := by omega
        have h_mod18 : (18 * n) % 10 = 6 := by omega
        have h_18div : (18 * n) / 10 = 18 * (n / 10) + 3 := by omega
        rw [h_mod18, h_18div] at h18
        have h_sum18_eq : sum_digits_10 (18 * (n / 10) + 3) = 3 := by omega
        have h_odd : (6 * (n / 10) + 1) % 2 = 1 := by omega
        have h_odd_four := sum_digits_odd_four (6 * (n / 10) + 1) h_sum6_eq h_odd
        have h_eq_3 : 3 * (6 * (n / 10) + 1) = 18 * (n / 10) + 3 := by omega
        rw [h_eq_3] at h_odd_four
        omega
      · have h_mod6 : (6 * n) % 10 = 8 := by omega
        omega
      · sorry
      · sorry
      · have h_mod6 : (6 * n) % 10 = 6 := by omega
        have h_6div : (6 * n) / 10 = 6 * (n / 10) + 3 := by omega
        rw [h_mod6, h_6div] at h6
        have h_sum6_eq : sum_digits_10 (6 * (n / 10) + 3) = 0 := by omega
        have h_eq : 6 * (n / 10) + 3 = 0 := sum_digits_eq_zero _ h_sum6_eq
        omega
      · have h_mod6 : (6 * n) % 10 = 2 := by omega
        have h_6div : (6 * n) / 10 = 6 * (n / 10) + 4 := by omega
        rw [h_mod6, h_6div] at h6
        have h_sum6_eq : sum_digits_10 (6 * (n / 10) + 4) = 4 := by omega
        have h_mod18 : (18 * n) % 10 = 6 := by omega
        have h_18div : (18 * n) / 10 = 18 * (n / 10) + 12 := by omega
        rw [h_mod18, h_18div] at h18
        have h_sum18_eq : sum_digits_10 (18 * (n / 10) + 12) = 3 := by omega
        have h_q_eq : 2 * (3 * (n / 10) + 2) = 6 * (n / 10) + 4 := by omega
        have h_6q_eq : 6 * (3 * (n / 10) + 2) = 18 * (n / 10) + 12 := by omega
        have h_2q_sum : sum_digits_10 (2 * (3 * (n / 10) + 2)) = 4 := by
          rw [h_q_eq]
          exact h_sum6_eq
        have h_6q_sum : sum_digits_10 (6 * (3 * (n / 10) + 2)) = 3 := by
          rw [h_6q_eq]
          exact h_sum18_eq
        have h_q_sum := sum_digits_four_six (3 * (n / 10) + 2) h_2q_sum h_6q_sum
        left
        have h_3q_eq : 3 * (3 * (n / 10) + 2) = 9 * (n / 10) + 6 := by omega
        have h_3q_sum := sum_digits_six_mul (3 * (n / 10) + 2) h_q_sum
        have h_9n_eq : 9 * n = 10 * (9 * (n / 10) + 6) + 3 := by omega
        have h_sum9 : sum_digits_10 (9 * n) = 3 + sum_digits_10 (9 * (n / 10) + 6) := by
          change (digits 10 (9 * n)).sum = 3 + (digits 10 (9 * (n / 10) + 6)).sum
          rw [h_9n_eq]
          rw [digits_eq_cons_digits_div (b := 10) (by decide)]
          · have h_mod : (10 * (9 * (n / 10) + 6) + 3) % 10 = 3 := by omega
            have h_div : (10 * (9 * (n / 10) + 6) + 3) / 10 = 9 * (n / 10) + 6 := by omega
            rw [h_mod, h_div]
            rfl
          · omega
        rw [h_sum9]
        rw [← h_3q_eq]
        rw [h_3q_sum]
      · have h_mod6 : (6 * n) % 10 = 8 := by omega
        omega
      · sorry


/--
Conjecture: if A277223(n) < 12 then A277223(n) = 0 or 9.
A277223 a(n) is never 1, 2, 3, 4, 5 or 6. Conjecture: if a(n) < 12 then a(n) = 0 or 9. - _Robert Israel_, Oct 06 2016
-/
theorem A277223_conjecture (n : ℕ) :
  n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by
  intro hn h_lt
  by_cases hn3 : n % 3 = 1
  · by_cases hn1 : n = 1
    · subst hn1
      right
      exact A277223_one
    · -- n >= 4 and n % 3 = 1
      have hn4 : n ≥ 4 := by omega
      have h_zero : A277223 n = 0 ∨ A277223 n > 0 := by omega
      rcases h_zero with h_zero | h_pos
      · left; exact h_zero
      · right
        unfold A277223 at h_pos h_lt
        have h_not_bdd : ¬ BddAbove { k | k = sum_digits_10 (k * n) } → sSup { k | k = sum_digits_10 (k * n) } = 0 := by
          exact sSup_of_not_bddAbove
        have h_bdd : BddAbove { k | k = sum_digits_10 (k * n) } := by
          by_contra h_nbdd
          have h_zero' := h_not_bdd h_nbdd
          generalize hK : sSup { k | k = sum_digits_10 (k * n) } = K at h_zero' h_pos
          omega
        have h_mem : sSup { k | k = sum_digits_10 (k * n) } ∈ { k | k = sum_digits_10 (k * n) } := by
          have h_nonempty : { k | k = sum_digits_10 (k * n) }.Nonempty := ⟨0, by simp [sum_digits_10]⟩
          exact sSup_mem h_nonempty h_bdd
        simp at h_mem
        obtain ⟨K, hK⟩ : ∃ K, sSup { k | k = sum_digits_10 (k * n) } = K := ⟨_, rfl⟩
        have h_mem_eq : K = sum_digits_10 (K * n) := by
          have h_eq := h_mem
          rw [hK] at h_eq
          exact h_eq
        have h_lt_eq : K < 12 := by
          have h_eq := h_lt
          rw [hK] at h_eq
          exact h_eq
        have h_pos_eq : K > 0 := by
          have h_eq := h_pos
          rw [hK] at h_eq
          exact h_eq
        clear h_lt h_pos h_mem
        by_cases h_sum1 : sum_digits_10 n = 1
        · have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by
            simp
            exact (sum_digits_one n h_sum1).symm
          have h9_le : 9 ≤ K := by
            rw [← hK]
            exact le_csSup h_bdd h9_mem
          by_contra h_ne9
          have h_ne9_K : K ≠ 9 := by
            intro h_eq
            apply h_ne9
            change sSup { k | k = sum_digits_10 (k * n) } = 9
            rw [hK]
            exact h_eq
          have hk : K = 10 ∨ K = 11 := by omega
          rcases hk with rfl | rfl
          · rw [sum_digits_10_mul_10] at h_mem_eq
            omega
          · have h11 := sum_digits_eleven_mul n h_sum1
            omega
        · -- sum_digits_10 n > 1
          by_contra h_ne9
          have h_ne9_K : K ≠ 9 := by
            intro h_eq
            apply h_ne9
            change sSup { k | k = sum_digits_10 (k * n) } = 9
            rw [hK]
            exact h_eq
          have h_sum_gt1 : sum_digits_10 n ≥ 2 := by
            have h_eq0 : sum_digits_10 n ≠ 0 := by
              intro h0
              have := sum_digits_eq_zero n h0
              omega
            omega
          by_cases hn9 : n % 9 = 1
          · -- n % 9 = 1
            sorry
          · -- n % 9 ≠ 1
            have hk_3_6 : K = 3 ∨ K = 6 := by
              by_contra h_not
              have hk : K = 1 ∨ K = 2 ∨ K = 4 ∨ K = 5 ∨ K = 7 ∨ K = 8 ∨ K = 10 ∨ K = 11 := by omega
              have h_not_valid := k_notin_valid_multipliers_9 n K hn9 hk
              exact h_not_valid h_mem_eq
            rcases hk_3_6 with rfl | rfl
            · -- K = 3
              have h3_mul : sum_digits_10 (9 * n) = 9 := by
                have h_eq : 9 * n = 3 * (3 * n) := by omega
                rw [h_eq]
                exact sum_digits_three (3 * n) h_mem_eq.symm
              have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h3_mul.symm
              have h9_le : 9 ≤ 3 := by
                rw [← hK]
                exact le_csSup h_bdd h9_mem
              omega
            · -- K = 6
              have h6_mul := sum_digits_six (6 * n) h_mem_eq.symm
              rcases h6_mul with h9 | h18
              · have h18_n : sum_digits_10 (18 * n) = 9 := by
                  have : 18 * n = 3 * (6 * n) := by omega
                  rw [this]
                  exact h9
                have h_contradiction := sum_digits_six_contradiction n h_mem_eq.symm h18_n
                rcases h_contradiction with h9_valid | h15_valid
                · have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by
                    simp
                    exact h9_valid.symm
                  have h9_le : 9 ≤ 6 := by
                    rw [← hK]
                    exact le_csSup h_bdd h9_mem
                  omega
                · have h15_mem : 15 ∈ { k | k = sum_digits_10 (k * n) } := by
                    simp
                    exact h15_valid.symm
                  have h15_le : 15 ≤ 6 := by
                    rw [← hK]
                    exact le_csSup h_bdd h15_mem
                  omega
              · have h18_mem : 18 ∈ { k | k = sum_digits_10 (k * n) } := by
                  simp
                  have : 18 * n = 3 * (6 * n) := by omega
                  rw [this]
                  exact h18.symm
                have h18_le : 18 ≤ 6 := by
                  rw [← hK]
                  exact le_csSup h_bdd h18_mem
                omega
  · -- n % 3 ≠ 1
    have h_zero : A277223 n = 0 ∨ A277223 n > 0 := by omega
    rcases h_zero with h_zero | h_pos
    · left; exact h_zero
    · right
      unfold A277223 at h_pos h_lt
      have h_not_bdd : ¬ BddAbove { k | k = sum_digits_10 (k * n) } → sSup { k | k = sum_digits_10 (k * n) } = 0 := by
        exact sSup_of_not_bddAbove
      have h_bdd : BddAbove { k | k = sum_digits_10 (k * n) } := by
        by_contra h_nbdd
        have h_zero' := h_not_bdd h_nbdd
        generalize hK : sSup { k | k = sum_digits_10 (k * n) } = K at h_zero' h_pos
        omega
      have h_mem : sSup { k | k = sum_digits_10 (k * n) } ∈ { k | k = sum_digits_10 (k * n) } := by
        have h_nonempty : { k | k = sum_digits_10 (k * n) }.Nonempty := ⟨0, by simp [sum_digits_10]⟩
        exact sSup_mem h_nonempty h_bdd
      simp at h_mem
      unfold A277223
      by_contra h_ne_9
      generalize hK : sSup { k | k = sum_digits_10 (k * n) } = K at h_mem h_lt h_pos h_ne_9
      have hk : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 ∨ K = 6 ∨ K = 7 ∨ K = 8 ∨ K = 10 ∨ K = 11 := by omega
      rw [← hK] at hk h_mem
      have h_not := k_notin_valid_multipliers n (sSup { k | k = sum_digits_10 (k * n) }) hn3 hk
      exact h_not h_mem
