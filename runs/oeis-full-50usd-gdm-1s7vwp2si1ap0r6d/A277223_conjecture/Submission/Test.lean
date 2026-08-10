import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

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

lemma sum_digits_10_3 : sum_digits_10 3 = 3 := by
  change (digits 10 3).sum = 3
  rw [digits_of_lt 10 3 (by decide) (by decide)]
  rfl

lemma sum_digits_10_6 : sum_digits_10 6 = 6 := by
  change (digits 10 6).sum = 6
  rw [digits_of_lt 10 6 (by decide) (by decide)]
  rfl

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


lemma sum_digits_mod_9 (m : ℕ) : sum_digits_10 m ≡ m [MOD 9] := by
  exact (modEq_digits_sum 9 10 (by rfl) m).symm

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
                rfl
              · omega
            rw [h_sum18']
            have h_div_eq : (2 * n) / 10 = 2 * (n / 10) + 1 := by omega
            rw [h_div_eq] at h2_div
            exact sum_digits_odd_18 (n / 10) h2_div
          exact h_sum18


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
          have hk_cases : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 ∨ K = 6 ∨ K = 7 ∨ K = 8 ∨ K = 10 ∨ K = 11 := by omega
          rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [one_mul] at h_mem_eq; exact h_sum1 h_mem_eq.symm
          · have h2_cases := sum_digits_two_cases n h_mem_eq.symm
            rcases h2_cases with h18 | h9
            · have h18_mem : 18 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h18.symm
              have h18_le : 18 ≤ 2 := by
                rw [← hK]
                exact le_csSup h_bdd h18_mem
              omega
            · have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h9.symm
              have h9_le : 9 ≤ 2 := by
                rw [← hK]
                exact le_csSup h_bdd h9_mem
              omega
          · have h3_mul : sum_digits_10 (9 * n) = 9 := by
              have h_eq : 9 * n = 3 * (3 * n) := by omega
              rw [h_eq]
              exact sum_digits_three (3 * n) h_mem_eq.symm
            have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h3_mul.symm
            have h9_le : 9 ≤ 3 := by
              rw [← hK]
              exact le_csSup h_bdd h9_mem
            omega
          · have h4_mul := sum_digits_four_mul (4 * n) h_mem_eq.symm
            rcases h4_mul with h12 | h12
            · have h2_n : sum_digits_10 (2 * n) = 2 := by
                have h1 : sum_digits_10 (2 * (2 * n)) = 4 := by
                  have : 2 * (2 * n) = 4 * n := by omega
                  rw [this]
                  exact h_mem_eq.symm
                have h2 : sum_digits_10 (6 * (2 * n)) = 3 := by
                  have : 6 * (2 * n) = 3 * (4 * n) := by omega
                  rw [this]
                  exact h12
                exact sum_digits_four_six (2 * n) h1 h2
              have h2_cases := sum_digits_two_cases n h2_n
              rcases h2_cases with h18 | h9
              · have h18_mem : 18 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h18.symm
                have h18_le : 18 ≤ 4 := by
                  rw [← hK]
                  exact le_csSup h_bdd h18_mem
                omega
              · have h9_mem : 9 ∈ { k | k = sum_digits_10 (k * n) } := by simp; exact h9.symm
                have h9_le : 9 ≤ 4 := by
                  rw [← hK]
                  exact le_csSup h_bdd h9_mem
                omega
            · have h12_mem : 12 ∈ { k | k = sum_digits_10 (k * n) } := by
                simp
                have : 12 * n = 3 * (4 * n) := by omega
                rw [this]
                exact h12.symm
              have h12_le : 12 ≤ 4 := by
                rw [← hK]
                exact le_csSup h_bdd h12_mem
              omega
          · have h5_mul := sum_digits_five_mul (5 * n) h_mem_eq.symm
            rcases h5_mul with h15 | h15
            · sorry
            · have h15_mem : 15 ∈ { k | k = sum_digits_10 (k * n) } := by
                simp
                have : 15 * n = 3 * (5 * n) := by omega
                rw [this]
                exact h15.symm
              have h15_le : 15 ≤ 5 := by
                rw [← hK]
                exact le_csSup h_bdd h15_mem
              omega
          · have h6_mul := sum_digits_six (6 * n) h_mem_eq.symm
            rcases h6_mul with h9 | h18
            · sorry
            · have h18_mem : 18 ∈ { k | k = sum_digits_10 (k * n) } := by
                simp
                have : 18 * n = 3 * (6 * n) := by omega
                rw [this]
                exact h18.symm
              have h18_le : 18 ≤ 6 := by
                rw [← hK]
                exact le_csSup h_bdd h18_mem
              omega
          · sorry
          · sorry
          · sorry
          · sorry
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
