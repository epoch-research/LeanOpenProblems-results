import FormalConjectures.Util.ProblemImports

open Nat Int Rat

noncomputable def A275460_rational : ℕ → ℚ
  | 0 => 1
  | Nat.succ k =>
    let n : ℕ := k + 1
    let a_prev : ℚ := A275460_rational k
    let n_q : ℚ := n.cast
    let num : ℚ := 3 * (9 * n_q - 7) * (9 * n_q - 5) * (9 * n_q - 2)
    let den : ℚ := n_q^2 * (3 * n_q - 2)
    a_prev * (num / den)

lemma den_factor_ne_zero (k : ℕ) : 3 * (k + 1 : ℚ) - 2 ≠ 0 := by
  have : 3 * (k + 1 : ℚ) - 2 = 3 * (k : ℚ) + 1 := by ring
  rw [this]
  have : 0 ≤ (k : ℚ) := by positivity
  linarith

lemma den_ne_zero (k : ℕ) : (k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) ≠ 0 := by
  have h1 : (k + 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have h2 : 3 * (k + 1 : ℚ) - 2 ≠ 0 := den_factor_ne_zero k
  exact mul_ne_zero (pow_ne_zero 2 h1) h2

theorem rational_recurrence (k : ℕ) :
  ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)) * A275460_rational (k + 1) =
  A275460_rational k * (3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2)) := by
  dsimp [A275460_rational]
  push_cast
  have h_den : (k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) ≠ 0 := den_ne_zero k
  have h_eq : (k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) *
    (A275460_rational k * (3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) /
      ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)))) =
    A275460_rational k * ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) *
      (3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) /
        ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)))) := by ring
  rw [h_eq]
  rw [mul_div_cancel₀ _ h_den]

lemma padicValRat_div (p : ℕ) [Fact p.Prime] (q r : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv r]
  ring




lemma padicValRat_num (p : ℕ) [Fact p.Prime] (k : ℕ) :
    padicValRat p (3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2)) =
    (padicValNat p 3 : ℤ) + (padicValNat p (9*k+2) : ℤ) + (padicValNat p (9*k+4) : ℤ) + (padicValNat p (9*k+7) : ℤ) := by
  have h1 : 9 * (k + 1 : ℚ) - 7 = ((9 * k + 2 : ℕ) : ℚ) := by push_cast; ring
  have h2 : 9 * (k + 1 : ℚ) - 5 = ((9 * k + 4 : ℕ) : ℚ) := by push_cast; ring
  have h3 : 9 * (k + 1 : ℚ) - 2 = ((9 * k + 7 : ℕ) : ℚ) := by push_cast; ring
  have h0 : (3 : ℚ) = ((3 : ℕ) : ℚ) := rfl
  rw [h1, h2, h3, h0]
  -- now we have a product of casts of: 3, 9*k+2, 9*k+4, 9*k+7
  have p0 : ((3 : ℕ) : ℚ) ≠ 0 := by norm_num
  have p1 : ((9*k+2 : ℕ) : ℚ) ≠ 0 := by positivity
  have p2 : ((9*k+4 : ℕ) : ℚ) ≠ 0 := by positivity
  have p3 : ((9*k+7 : ℕ) : ℚ) ≠ 0 := by positivity
  -- let's split the multiplications
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero p0 p1) p2) p3]
  rw [padicValRat.mul (mul_ne_zero p0 p1) p2]
  rw [padicValRat.mul p0 p1]
  -- now rewrite each using padicValRat_of_nat
  rw [← padicValRat_of_nat, ← padicValRat_of_nat, ← padicValRat_of_nat, ← padicValRat_of_nat]

lemma padicValRat_den (p : ℕ) [Fact p.Prime] (k : ℕ) :
    padicValRat p ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)) =
    2 * (padicValNat p (k + 1) : ℤ) + (padicValNat p (3*k+1) : ℤ) := by
  have h1 : 3 * (k + 1 : ℚ) - 2 = ((3 * k + 1 : ℕ) : ℚ) := by push_cast; ring
  have h2 : (k + 1 : ℚ)^2 = ((k + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [h1, h2]
  have p1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have p2 : ((3*k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [padicValRat.mul (mul_ne_zero p1 p1) p2]
  rw [padicValRat.mul p1 p1]
  simp_rw [← padicValRat_of_nat]
  ring


lemma A275460_rational_ne_zero (n : ℕ) : A275460_rational n ≠ 0 := by
  induction n with
  | zero =>
    dsimp [A275460_rational]
    exact one_ne_zero
  | succ k ih =>
    dsimp [A275460_rational]
    push_cast
    have h_num : 3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) ≠ 0 := by
      have h1 : 9 * (k + 1 : ℚ) - 7 = 9 * (k : ℚ) + 2 := by ring
      have h2 : 9 * (k + 1 : ℚ) - 5 = 9 * (k : ℚ) + 4 := by ring
      have h3 : 9 * (k + 1 : ℚ) - 2 = 9 * (k : ℚ) + 7 := by ring
      rw [h1, h2, h3]
      have : 0 ≤ (k : ℚ) := by positivity
      have p0 : (3 : ℚ) ≠ 0 := by norm_num
      have p1 : 9 * (k : ℚ) + 2 ≠ 0 := by linarith
      have p2 : 9 * (k : ℚ) + 4 ≠ 0 := by linarith
      have p3 : 9 * (k : ℚ) + 7 ≠ 0 := by linarith
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero p0 p1) p2) p3
    have h_den : (k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) ≠ 0 := den_ne_zero k
    have h_div : 3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) / ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)) ≠ 0 :=
      div_ne_zero h_num h_den
    exact mul_ne_zero ih h_div


open Finset


lemma not_dvd_three_9k_plus_2 (k : ℕ) : ¬ 3 ∣ 9*k+2 := by
  rintro ⟨d, hd⟩
  omega

lemma not_dvd_three_9k_plus_4 (k : ℕ) : ¬ 3 ∣ 9*k+4 := by
  rintro ⟨d, hd⟩
  omega

lemma not_dvd_three_9k_plus_7 (k : ℕ) : ¬ 3 ∣ 9*k+7 := by
  rintro ⟨d, hd⟩
  omega

lemma not_dvd_three_3k_plus_1 (k : ℕ) : ¬ 3 ∣ 3*k+1 := by
  rintro ⟨d, hd⟩
  omega

lemma padicValRat_A275460 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicValRat p (A275460_rational n) =
    (n : ℤ) * padicValNat p 3 +
    (∑ k ∈ range n, ((padicValNat p (9*k+2) : ℤ) + (padicValNat p (9*k+4) : ℤ) + (padicValNat p (9*k+7) : ℤ))) -
    (∑ k ∈ range n, (padicValNat p (3*k+1) : ℤ)) -
    2 * (padicValNat p n.factorial : ℤ) := by
  induction n with
  | zero =>
    dsimp [A275460_rational]
    simp
  | succ k ih =>
    have h_num : 3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) ≠ 0 := by
      have h1 : 9 * (k + 1 : ℚ) - 7 = ((9 * k + 2 : ℕ) : ℚ) := by push_cast; ring
      have h2 : 9 * (k + 1 : ℚ) - 5 = ((9 * k + 4 : ℕ) : ℚ) := by push_cast; ring
      have h3 : 9 * (k + 1 : ℚ) - 2 = ((9 * k + 7 : ℕ) : ℚ) := by push_cast; ring
      rw [h1, h2, h3]
      have p0 : ((3 : ℕ) : ℚ) ≠ 0 := by norm_num
      have p1 : ((9*k+2 : ℕ) : ℚ) ≠ 0 := by positivity
      have p2 : ((9*k+4 : ℕ) : ℚ) ≠ 0 := by positivity
      have p3 : ((9*k+7 : ℕ) : ℚ) ≠ 0 := by positivity
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero p0 p1) p2) p3
    have h_den : (k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2) ≠ 0 := den_ne_zero k
    have h_div : 3 * (9 * (k + 1 : ℚ) - 7) * (9 * (k + 1 : ℚ) - 5) * (9 * (k + 1 : ℚ) - 2) / ((k + 1 : ℚ)^2 * (3 * (k + 1 : ℚ) - 2)) ≠ 0 :=
      div_ne_zero h_num h_den
    dsimp [A275460_rational]
    have h_cast : (↑(k + 1) : ℚ) = (k + 1 : ℚ) := by push_cast; rfl
    rw [h_cast]
    rw [padicValRat.mul (A275460_rational_ne_zero k) h_div]


    rw [padicValRat_div p _ _ h_num h_den]
    rw [padicValRat_num p k, padicValRat_den p k]
    rw [ih]
    have h_fact : (k + 1).factorial = (k + 1) * k.factorial := rfl
    rw [h_fact]
    have fk : k.factorial ≠ 0 := factorial_ne_zero k
    rw [padicValNat.mul (succ_ne_zero k) fk]
    rw [sum_range_succ, sum_range_succ]
    push_cast
    ring




lemma padicValRat_A275460_three (n : ℕ) : padicValRat 3 (A275460_rational n) ≥ 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicValRat_A275460 3 n]
  have h33 : padicValNat 3 3 = 1 := by
    have : 1 < 3 := by decide
    exact padicValNat.self this
  rw [h33]
  have h_sum1 : ∑ k ∈ range n, ((padicValNat 3 (9*k+2) : ℤ) + (padicValNat 3 (9*k+4) : ℤ) + (padicValNat 3 (9*k+7) : ℤ)) = 0 := by
    apply sum_eq_zero
    intro k _
    rw [padicValNat.eq_zero_of_not_dvd (not_dvd_three_9k_plus_2 k)]
    rw [padicValNat.eq_zero_of_not_dvd (not_dvd_three_9k_plus_4 k)]
    rw [padicValNat.eq_zero_of_not_dvd (not_dvd_three_9k_plus_7 k)]
    simp
  have h_sum2 : ∑ k ∈ range n, (padicValNat 3 (3*k+1) : ℤ) = 0 := by
    apply sum_eq_zero
    intro k _
    rw [padicValNat.eq_zero_of_not_dvd (not_dvd_three_3k_plus_1 k)]
    simp
  rw [h_sum1, h_sum2]
  simp only [add_zero, zero_sub, Nat.cast_one, mul_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h_val := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 hn
    have : (3 - 1) * padicValNat 3 n.factorial = 2 * padicValNat 3 n.factorial := rfl
    rw [this] at h_val
    omega


lemma padicValNat_le_self (p x : ℕ) [hp : Fact p.Prime] (hx : x ≠ 0) : padicValNat p x ≤ x := by
  have h_dvd : p ^ padicValNat p x ∣ x := (padicValNat_dvd_iff_le hx).mpr (le_refl _)
  have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) h_dvd
  have h_pow_le : padicValNat p x ≤ p ^ padicValNat p x := by
    have : 1 < p := hp.out.one_lt
    exact (Nat.lt_pow_self this).le
  omega

lemma padicValNat_eq_sum_dvd (p : ℕ) [hp : Fact p.Prime] (x : ℕ) (hx : x ≠ 0) :
    (padicValNat p x : ℤ) = ∑ j ∈ Ico 1 (x + 1), if p^j ∣ x then (1 : ℤ) else 0 := by
  let k := padicValNat p x
  have hk_le : k ≤ x := padicValNat_le_self p x hx
  have h_split : Ico 1 (x + 1) = Ico 1 (k + 1) ∪ Ico (k + 1) (x + 1) := by
    rw [Finset.Ico_union_Ico_eq_Ico]
    · omega
    · omega
  rw [h_split, sum_union]
  · have h_sum1 : ∑ j ∈ Ico 1 (k + 1), (if p^j ∣ x then (1 : ℤ) else 0) = ∑ j ∈ Ico 1 (k + 1), (1 : ℤ) := by
      apply sum_congr rfl
      intro j hj
      rw [mem_Ico] at hj
      have hj_le : j ≤ k := by omega
      have h_dvd : p^j ∣ x := by
        rw [padicValNat_dvd_iff_le hx]
        exact hj_le
      rw [if_pos h_dvd]
    have h_sum2 : ∑ j ∈ Ico (k + 1) (x + 1), (if p^j ∣ x then (1 : ℤ) else 0) = ∑ j ∈ Ico (k + 1) (x + 1), (0 : ℤ) := by
      apply sum_congr rfl
      intro j hj
      rw [mem_Ico] at hj
      have hj_gt : j > k := by omega
      have h_not_dvd : ¬ p^j ∣ x := by
        intro h
        rw [padicValNat_dvd_iff_le hx] at h
        omega
      rw [if_neg h_not_dvd]
    have hk1 : card (Ico 1 (k + 1)) = k := by
      rw [Nat.card_Ico]
      omega
    rw [h_sum1, h_sum2, sum_const, sum_const, nsmul_zero, add_zero]
    rw [hk1]
    simp only [nsmul_one]
    omega
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega


lemma padicValNat_eq_sum_dvd_of_lt (p : ℕ) [hp : Fact p.Prime] {B : ℕ} (x : ℕ) (hx : x ≠ 0) (h_lt : x < B) :
    (padicValNat p x : ℤ) = ∑ j ∈ Ico 1 B, if p^j ∣ x then (1 : ℤ) else 0 := by
  have h_split : Ico 1 B = Ico 1 (x + 1) ∪ Ico (x + 1) B := by
    rw [Finset.Ico_union_Ico_eq_Ico]
    · omega
    · omega
  rw [h_split, sum_union]
  · rw [← padicValNat_eq_sum_dvd p x hx]
    have h_zero : ∑ j ∈ Ico (x + 1) B, (if p^j ∣ x then (1 : ℤ) else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [mem_Ico] at hj
      have hj_gt : j > padicValNat p x := by
        have : padicValNat p x ≤ x := padicValNat_le_self p x hx
        omega
      have h_not_dvd : ¬ p^j ∣ x := by
        intro h
        rw [padicValNat_dvd_iff_le hx] at h
        omega
      rw [if_neg h_not_dvd]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega


lemma r3_ge_min_of_eq (D y k : ℕ) (hD : D ≥ 2) (hy : y < D) (hk : k < 9) (h_eq : 9 * y + 1 = (9 - k) * D) :
    (3 * y) % D ≥ (2 * y) % D ∨ (3 * y) % D ≥ (4 * y) % D ∨ (3 * y) % D ≥ (7 * y) % D := by
  have h_not_3 : ¬ 3 ∣ (9 - k) := by
    intro h3
    have h_dvd : 3 ∣ 9 * y + 1 := by
      rw [h_eq]
      exact dvd_mul_of_dvd_left h3 D
    have h_dvd9 : 3 ∣ 9 * y := dvd_mul_of_dvd_left (by decide) y
    omega
  interval_cases k
  · omega
  · right; left
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      have h_div : 3 * y - 2 * D = (6 * D - 3) / 9 := by
        have : 6 * D - 3 = 9 * (3 * y - 2 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (6 * D - 3) / 9 + 2 * D := by omega
      have h_lt : (6 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod4 : (4 * y) % D = (5 * D - 4) / 9 := by
      have h_div : 4 * y - 3 * D = (5 * D - 4) / 9 := by
        have : 5 * D - 4 = 9 * (4 * y - 3 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 4 * y = (5 * D - 4) / 9 + 3 * D := by omega
      have h_lt : (5 * D - 4) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod4]
    omega
  · right; left
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      have h_div : 3 * y - 2 * D = (3 * D - 3) / 9 := by
        have : 3 * D - 3 = 9 * (3 * y - 2 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (3 * D - 3) / 9 + 2 * D := by omega
      have h_lt : (3 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod4 : (4 * y) % D = (D - 4) / 9 := by
      have h_div : 4 * y - 3 * D = (D - 4) / 9 := by
        have : D - 4 = 9 * (4 * y - 3 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 4 * y = (D - 4) / 9 + 3 * D := by omega
      have h_lt : (D - 4) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod4]
    omega
  · omega
  · right; left
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      have h_div : 3 * y - 1 * D = (6 * D - 3) / 9 := by
        have : 6 * D - 3 = 9 * (3 * y - 1 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (6 * D - 3) / 9 + 1 * D := by omega
      have h_lt : (6 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod4 : (4 * y) % D = (2 * D - 4) / 9 := by
      have h_div : 4 * y - 2 * D = (2 * D - 4) / 9 := by
        have : 2 * D - 4 = 9 * (4 * y - 2 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 4 * y = (2 * D - 4) / 9 + 2 * D := by omega
      have h_lt : (2 * D - 4) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod4]
    omega
  · right; right
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      have h_div : 3 * y - 1 * D = (3 * D - 3) / 9 := by
        have : 3 * D - 3 = 9 * (3 * y - 1 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (3 * D - 3) / 9 + 1 * D := by omega
      have h_lt : (3 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod7 : (7 * y) % D = (D - 7) / 9 := by
      have h_div : 7 * y - 3 * D = (D - 7) / 9 := by
        have : D - 7 = 9 * (7 * y - 3 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 7 * y = (D - 7) / 9 + 3 * D := by omega
      have h_lt : (D - 7) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod7]
    omega
  · omega
  · right; right
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      have h_div : 3 * y - 0 * D = (6 * D - 3) / 9 := by
        have : 6 * D - 3 = 9 * (3 * y - 0 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (6 * D - 3) / 9 + 0 * D := by omega
      have h_lt : (6 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod7 : (7 * y) % D = (5 * D - 7) / 9 := by
      have h_div : 7 * y - 1 * D = (5 * D - 7) / 9 := by
        have : 5 * D - 7 = 9 * (7 * y - 1 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 7 * y = (5 * D - 7) / 9 + 1 * D := by omega
      have h_lt : (5 * D - 7) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod7]
    omega
  · left
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      have h_div : 3 * y - 0 * D = (3 * D - 3) / 9 := by
        have : 3 * D - 3 = 9 * (3 * y - 0 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 3 * y = (3 * D - 3) / 9 + 0 * D := by omega
      have h_lt : (3 * D - 3) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_mod2 : (2 * y) % D = (2 * D - 2) / 9 := by
      have h_div : 2 * y - 0 * D = (2 * D - 2) / 9 := by
        have : 2 * D - 2 = 9 * (2 * y - 0 * D) := by omega
        rw [this, Nat.mul_div_cancel_left _ (by decide)]
      have h_sum : 2 * y = (2 * D - 2) / 9 + 0 * D := by omega
      have h_lt : (2 * D - 2) / 9 < D := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      rw [h_sum]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    rw [h_mod3, h_mod2]
    omega


lemma coprime_nine_pow (p j : ℕ) [hp : Fact p.Prime] (hne : p ≠ 3) : Nat.Coprime 9 (p^j) := by
  have h_prime : p.Prime := hp.out
  have h_coprime_9_p : Nat.Coprime 9 p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    have h_gcd_dvdp : p.gcd 9 ∣ p := Nat.gcd_dvd_left p 9
    rcases h_prime.eq_one_or_self_of_dvd _ h_gcd_dvdp with h1 | h2
    · exact h1
    · have hp3 : p = 3 := by
        have h_dvd9 : p ∣ 9 := by
          have : p.gcd 9 = p := h2
          rw [← this]
          exact Nat.gcd_dvd_right p 9
        have : p ∣ 3 * 3 := h_dvd9
        have h_prime3 : Nat.Prime 3 := by decide
        rcases h_prime.dvd_mul.mp this with hp3_1 | hp3_2
        · rcases h_prime3.eq_one_or_self_of_dvd _ hp3_1 with h_one | h_self
          · rw [h_one] at h_prime; linarith [h_prime.two_le]
          · exact h_self
        · rcases h_prime3.eq_one_or_self_of_dvd _ hp3_2 with h_one | h_self
          · rw [h_one] at h_prime; linarith [h_prime.two_le]
          · exact h_self
      exact (hne hp3).elim
  exact Nat.Coprime.pow_right j h_coprime_9_p

lemma padicValNat_three_eq_zero_of_ne_three (p : ℕ) [hp : Fact p.Prime] (hne : p ≠ 3) : padicValNat p 3 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have hp_dvd3 : p ∣ 3 := hdvd
  have h_prime : p.Prime := hp.out
  rcases Nat.Prime.eq_one_or_self_of_dvd h_prime hp_dvd3 with hp1 | hpeq
  · linarith [h_prime.two_le]
  · exact hne hpeq

lemma sum_residue_eq (D n r : ℕ) (hD : D ≠ 0) (hr : r < D) :
    ∑ k ∈ range n, (if k % D = r then (1 : ℤ) else 0) = (n / D : ℤ) + (if r < n % D then 1 else 0) := by
  induction n with
  | zero =>
    simp [Nat.zero_div, Nat.zero_mod]
  | succ k ih =>
    rw [sum_range_succ, ih]
    have h_div_mod : (k + 1) / D = k / D + if (k % D + 1 = D) then 1 else 0 := by
      omega
    have h_mod : (k + 1) % D = if (k % D + 1 = D) then 0 else k % D + 1 := by
      omega
    rw [h_div_mod, h_mod]
    push_cast
    split_ifs <;> omega

lemma count_residue_le (D n r1 r2 : ℕ) (hr : r1 ≤ r2) (hD : D ≠ 0) (hr2 : r2 < D) :
    ∑ k ∈ range n, (if k % D = r1 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) := by
  have hr1 : r1 < D := by omega
  rw [sum_residue_eq D n r1 hD hr1]
  rw [sum_residue_eq D n r2 hD hr2]
  split_ifs <;> omega

lemma count_ineq (D n r2 r3 r4 r7 : ℕ) (hD : D ≠ 0) (hr2 : r2 < D) (hr3 : r3 < D) (hr4 : r4 < D) (hr7 : r7 < D)
    (h_or : r3 ≥ r2 ∨ r3 ≥ r4 ∨ r3 ≥ r7) :
    ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥
    ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) +
    2 * ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) := by
  have h_den_le2 : r2 ≤ D - 1 := by omega
  have h_den_le4 : r4 ≤ D - 1 := by omega
  have h_den_le7 : r7 ≤ D - 1 := by omega
  have h_le2 : ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r2 (D - 1) h_den_le2 hD (by omega)
  have h_le4 : ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r4 (D - 1) h_den_le4 hD (by omega)
  have h_le7 : ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r7 (D - 1) h_den_le7 hD (by omega)
  rcases h_or with h | h | h
  · have h_count : ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r2 r3 h hD hr3
    omega
  · have h_count : ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r4 r3 h hD hr3
    omega
  · have h_count : ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r7 r3 h hD hr3
    omega


lemma dvd_iff_eq_zero (D x : ℕ) [NeZero D] : D ∣ x ↔ (x : ZMod D) = 0 := by
  exact (CharP.cast_eq_zero_iff (ZMod D) D x).symm

lemma zmod_eq_iff_mod_eq (D k a y : ℕ) [NeZero D] :
    (k : ZMod D) = (a * y : ZMod D) ↔ k % D = (a * y) % D := by
  have h_val_k : (k : ZMod D).val = k % D := ZMod.val_natCast D k
  have h_val_ay : (a * y : ZMod D).val = (a * y) % D := by
    have : (a * y : ZMod D) = ((a * y : ℕ) : ZMod D) := by push_cast; rfl
    rw [this, ZMod.val_natCast D (a * y)]
  have h_inj := @ZMod.val_injective D _
  rw [← h_inj.eq_iff]
  rw [h_val_k, h_val_ay]



lemma dvd_iff_mod_eq_r_val (D y k' k a : ℕ) [hD : NeZero D] (h_eq : 9 * y + 1 = (9 - k') * D) :
    D ∣ 9 * k + a ↔ k % D = (a * y) % D := by
  constructor
  · intro h_div
    rcases h_div with ⟨c, hc⟩
    have hc' : 9 * k + a = c * D := by
      rw [hc, mul_comm]
    have h_ident : a * y + (9 - k') * D * k = k + c * y * D := by
      calc a * y + (9 - k') * D * k
        _ = a * y + (9 * y + 1) * k := by rw [← h_eq]
        _ = y * (9 * k + a) + k := by ring
        _ = y * (c * D) + k := by rw [hc']
        _ = k + c * y * D := by ring
    have h_mod : (a * y + (9 - k') * D * k) % D = (k + c * y * D) % D := by rw [h_ident]
    have h_mod' : a * y % D = k % D := by
      calc a * y % D
        _ = (a * y + D * ((9 - k') * k)) % D := by rw [Nat.add_mul_mod_self_left]
        _ = (a * y + (9 - k') * D * k) % D := by congr 1; ring
        _ = (k + c * y * D) % D := h_mod
        _ = (k + D * (c * y)) % D := by congr 1; ring
        _ = k % D := by rw [Nat.add_mul_mod_self_left]
    exact h_mod'.symm
  · intro h_mod
    rw [dvd_iff_eq_zero]
    have h_eq_zmod : (k : ZMod D) = (a * y : ZMod D) := by
      rw [zmod_eq_iff_mod_eq]
      exact h_mod
    have h_cast : ((9 * k + a : ℕ) : ZMod D) = 9 * (k : ZMod D) + a := by push_cast; rfl
    have h_eq0 : ((9 * y + 1 : ℕ) : ZMod D) = 0 := by
      rw [← dvd_iff_eq_zero]
      exact ⟨9 - k', by rw [h_eq, mul_comm]⟩
    have h_eq0_cast : 9 * (y : ZMod D) + 1 = 0 := by
      have : ((9 * y + 1 : ℕ) : ZMod D) = 9 * (y : ZMod D) + 1 := by push_cast; rfl
      rw [← this, h_eq0]
    rw [h_cast]
    calc 9 * (k : ZMod D) + a
      _ = 9 * (a * y : ZMod D) + a := by rw [h_eq_zmod]
      _ = a * (9 * y + 1) := by ring
      _ = a * 0 := by rw [h_eq0_cast]
      _ = 0 := by ring

lemma exists_y_mod (D : ℕ) (hD : D ≥ 2) (h_coprime : Nat.Coprime 9 D) :
    ∃ y < D, (9 * y) % D = D - 1 := by
  haveI : NeZero D := ⟨by omega⟩
  have hu : IsUnit (9 : ZMod D) := (ZMod.isUnit_iff_coprime 9 D).mpr h_coprime
  let u := hu.unit
  let y' : ZMod D := - ((u⁻¹ : (ZMod D)ˣ) : ZMod D)
  let y := y'.val
  use y
  constructor
  · exact ZMod.val_lt y'
  · have h1 : (u : ZMod D) * (- ((u⁻¹ : (ZMod D)ˣ) : ZMod D)) = -1 := by
      have h_u_inv : (u : ZMod D) * ((u⁻¹ : (ZMod D)ˣ) : ZMod D) = 1 := u.mul_inv
      calc (u : ZMod D) * (- ((u⁻¹ : (ZMod D)ˣ) : ZMod D)) = - ((u : ZMod D) * ((u⁻¹ : (ZMod D)ˣ) : ZMod D)) := by ring
      _ = -1 := by rw [h_u_inv]
    have h2 : ((D - 1 : ℕ) : ZMod D) = -1 := by
      have h_self : ((D : ℕ) : ZMod D) = 0 := ZMod.natCast_self D
      have h_add : ((D - 1 : ℕ) : ZMod D) + 1 = 0 := by
        calc ((D - 1 : ℕ) : ZMod D) + 1 = ((D - 1 + 1 : ℕ) : ZMod D) := by push_cast; rfl
        _ = ((D : ℕ) : ZMod D) := by congr 1; omega
        _ = 0 := h_self
      calc ((D - 1 : ℕ) : ZMod D) = ((D - 1 : ℕ) : ZMod D) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h_add]
      _ = -1 := by ring
    have h_val : ((9 * y : ℕ) : ZMod D).val = D - 1 := by
      have h_val_eq : ((9 * y : ℕ) : ZMod D) = ((D - 1 : ℕ) : ZMod D) := by
        have hy_cast : (y : ZMod D) = y' := ZMod.natCast_zmod_val y'
        have h9_cast : (9 : ZMod D) = u := hu.unit_spec.symm
        calc ((9 * y : ℕ) : ZMod D) = 9 * (y : ZMod D) := by push_cast; rfl
        _ = (u : ZMod D) * y' := by rw [hy_cast, h9_cast]
        _ = -1 := h1
        _ = ((D - 1 : ℕ) : ZMod D) := h2.symm
      have h_val_eq2 := congr_arg ZMod.val h_val_eq
      rw [ZMod.val_natCast, ZMod.val_natCast] at h_val_eq2
      have hD1 : D - 1 < D := by omega
      rw [Nat.mod_eq_of_lt hD1] at h_val_eq2
      rw [ZMod.val_natCast]
      exact h_val_eq2
    rw [← h_val]
    exact (ZMod.val_natCast D (9 * y)).symm

lemma coprime_three_pow (p j : ℕ) [hp : Fact p.Prime] (hne : p ≠ 3) : Nat.Coprime 3 (p^j) := by
  have h_prime : p.Prime := hp.out
  have h_coprime_3_p : Nat.Coprime 3 p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    have h_gcd_dvdp : p.gcd 3 ∣ p := Nat.gcd_dvd_left p 3
    rcases h_prime.eq_one_or_self_of_dvd _ h_gcd_dvdp with h1 | h2
    · exact h1
    · have hp3 : p = 3 := by
        have h_dvd3 : p ∣ 3 := by
          have : p.gcd 3 = p := h2
          rw [← this]
          exact Nat.gcd_dvd_right p 3
        have h_prime3 : Nat.Prime 3 := by decide
        rcases h_prime3.eq_one_or_self_of_dvd _ h_dvd3 with h_one | h_self
        · rw [h_one] at h_prime; linarith [h_prime.two_le]
        · exact h_self
      exact (hne hp3).elim
  exact Nat.Coprime.pow_right j h_coprime_3_p

lemma dvd_three_k_plus_one_iff (p j y k' k : ℕ) [hp : Fact p.Prime] (hne : p ≠ 3) [hD : NeZero (p^j)] (h_eq : 9 * y + 1 = (9 - k') * p^j) :
    p^j ∣ 3 * k + 1 ↔ k % (p^j) = (3 * y) % (p^j) := by
  have h_cop : Nat.Coprime (p^j) 3 := (coprime_three_pow p j hne).symm
  have h_equiv : p^j ∣ 3 * k + 1 ↔ p^j ∣ 9 * k + 3 := by
    have : 9 * k + 3 = 3 * (3 * k + 1) := by ring
    rw [this]
    constructor
    · intro h
      exact dvd_mul_of_dvd_right h 3
    · exact h_cop.dvd_of_dvd_mul_left
  rw [h_equiv]
  exact dvd_iff_mod_eq_r_val (p^j) y k' k 3 h_eq



lemma dvd_succ_iff_mod_eq (D k : ℕ) [hD : NeZero D] (h_ge : D ≥ 2) : D ∣ k + 1 ↔ k % D = D - 1 := by
  have h2 : ((D - 1 : ℕ) : ZMod D) = -1 := by
    have h_self : ((D : ℕ) : ZMod D) = 0 := ZMod.natCast_self D
    have h_add : ((D - 1 : ℕ) : ZMod D) + 1 = 0 := by
      calc ((D - 1 : ℕ) : ZMod D) + 1 = ((D - 1 + 1 : ℕ) : ZMod D) := by push_cast; rfl
      _ = ((D : ℕ) : ZMod D) := by congr 1; omega
      _ = 0 := h_self
    calc ((D - 1 : ℕ) : ZMod D) = ((D - 1 : ℕ) : ZMod D) + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_add]
    _ = -1 := by ring
  rw [dvd_iff_eq_zero]
  have h_equiv : ((k + 1 : ℕ) : ZMod D) = 0 ↔ (k : ZMod D) = ((D - 1 : ℕ) : ZMod D) := by
    have h_cast_k : ((k + 1 : ℕ) : ZMod D) = (k : ZMod D) + 1 := by push_cast; rfl
    constructor
    · intro h
      rw [h_cast_k] at h
      calc (k : ZMod D) = k + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
      _ = ((D - 1 : ℕ) : ZMod D) := h2.symm
    · intro h
      rw [h_cast_k]
      calc (k : ZMod D) + 1 = ((D - 1 : ℕ) : ZMod D) + 1 := by rw [h]
      _ = -1 + 1 := by rw [h2]
      _ = 0 := by ring
  rw [h_equiv]
  have h_val_inj : (k : ZMod D) = ((D - 1 : ℕ) : ZMod D) ↔ k % D = (D - 1) % D := by
    have h_val_k : (k : ZMod D).val = k % D := ZMod.val_natCast D k
    have h_val_D1 : ((D - 1 : ℕ) : ZMod D).val = (D - 1) % D := ZMod.val_natCast D (D - 1)
    have h_inj : Function.Injective (ZMod.val : ZMod D → ℕ) := ZMod.val_injective D
    rw [← h_inj.eq_iff, h_val_k, h_val_D1]
  rw [h_val_inj]
  have hD1 : D - 1 < D := by omega
  rw [Nat.mod_eq_of_lt hD1]

lemma step_ineq (p : ℕ) [hp : Fact p.Prime] (hne : p ≠ 3) (j : ℕ) (hj : j ≥ 1) (n : ℕ) :
    ∑ k ∈ range n, (if p^j ∣ 9*k+2 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if p^j ∣ 9*k+4 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if p^j ∣ 9*k+7 then (1 : ℤ) else 0) ≥
    ∑ k ∈ range n, (if p^j ∣ 3*k+1 then (1 : ℤ) else 0) +
    2 * ∑ k ∈ range n, (if p^j ∣ k+1 then (1 : ℤ) else 0) := by
  let D := p^j
  have hD : D ≥ 2 := by
    have hp2 : p ≥ 2 := hp.out.two_le
    have : p^j ≥ p^1 := Nat.pow_le_pow_right (by omega) hj
    rw [pow_one] at this
    omega
  haveI : NeZero D := ⟨by omega⟩
  have h_cop : Nat.Coprime 9 D := coprime_nine_pow p j hne
  rcases exists_y_mod D hD h_cop with ⟨y, hy_lt, hy_eq⟩
  let m := (9 * y + 1) / D
  have hm_eq : 9 * y + 1 = m * D := by
    rw [Nat.div_add_mod (9 * y + 1) D]
    have h_mod0 : (9 * y + 1) % D = 0 := by
      calc (9 * y + 1) % D = (9 * y % D + 1) % D := by rw [Nat.add_mod]
      _ = (D - 1 + 1) % D := by rw [hy_eq]
      _ = D % D := by congr 1; omega
      _ = 0 := Nat.mod_self D
    rw [h_mod0, add_zero]
  have hm_lt : m < 9 := by
    have : 9 * y + 1 < 9 * D := by omega
    have : m * D < 9 * D := by rw [← hm_eq]; exact this
    exact Nat.lt_of_mul_lt_mul_right this
  have hm_ge1 : m ≥ 1 := by
    have : 9 * y + 1 ≥ 1 := by omega
    have : m * D ≥ 1 := by rw [← hm_eq]; exact this
    exact Nat.div_pos (by omega) (by omega)
  let k' := 9 - m
  have hk'_lt : k' < 9 := by omega
  have h_eq2 : 9 * y + 1 = (9 - k') * D := by
    have : 9 - k' = m := by omega
    rw [this, hm_eq]
  have h_r2 : ∀ k, (p^j ∣ 9 * k + 2) ↔ k % (p^j) = (2 * y) % (p^j) := fun k => dvd_iff_mod_eq_r_val (p^j) y k' k 2 h_eq2
  have h_r4 : ∀ k, (p^j ∣ 9 * k + 4) ↔ k % (p^j) = (4 * y) % (p^j) := fun k => dvd_iff_mod_eq_r_val (p^j) y k' k 4 h_eq2
  have h_r7 : ∀ k, (p^j ∣ 9 * k + 7) ↔ k % (p^j) = (7 * y) % (p^j) := fun k => dvd_iff_mod_eq_r_val (p^j) y k' k 7 h_eq2
  have h_r3 : ∀ k, (p^j ∣ 3 * k + 1) ↔ k % (p^j) = (3 * y) % (p^j) := fun k => dvd_three_k_plus_one_iff p j y k' k hne h_eq2
  have h_r1 : ∀ k, (p^j ∣ k + 1) ↔ k % (p^j) = p^j - 1 := fun k => dvd_succ_iff_mod_eq D k hD
  have h_sum2 : ∑ k ∈ range n, (if p^j ∣ 9 * k + 2 then (1 : ℤ) else 0) = ∑ k ∈ range n, (if k % D = (2 * y) % D then (1 : ℤ) else 0) := by
    apply sum_congr rfl; intro k _; rw [h_r2 k]
  have h_sum4 : ∑ k ∈ range n, (if p^j ∣ 9 * k + 4 then (1 : ℤ) else 0) = ∑ k ∈ range n, (if k % D = (4 * y) % D then (1 : ℤ) else 0) := by
    apply sum_congr rfl; intro k _; rw [h_r4 k]
  have h_sum7 : ∑ k ∈ range n, (if p^j ∣ 9 * k + 7 then (1 : ℤ) else 0) = ∑ k ∈ range n, (if k % D = (7 * y) % D then (1 : ℤ) else 0) := by
    apply sum_congr rfl; intro k _; rw [h_r7 k]
  have h_sum3 : ∑ k ∈ range n, (if p^j ∣ 3 * k + 1 then (1 : ℤ) else 0) = ∑ k ∈ range n, (if k % D = (3 * y) % D then (1 : ℤ) else 0) := by
    apply sum_congr rfl; intro k _; rw [h_r3 k]
  have h_sum1 : ∑ k ∈ range n, (if p^j ∣ k + 1 then (1 : ℤ) else 0) = ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) := by
    apply sum_congr rfl; intro k _; rw [h_r1 k]
  rw [h_sum2, h_sum4, h_sum7, h_sum3, h_sum1]
  have h_or : (3 * y) % D ≥ (2 * y) % D ∨ (3 * y) % D ≥ (4 * y) % D ∨ (3 * y) % D ≥ (7 * y) % D := r3_ge_min_of_eq D y k' hD hy_lt hk'_lt h_eq2
  have hr2 : (2 * y) % D < D := Nat.mod_lt _ (by omega)
  have hr3 : (3 * y) % D < D := Nat.mod_lt _ (by omega)
  have hr4 : (4 * y) % D < D := Nat.mod_lt _ (by omega)
  have hr7 : (7 * y) % D < D := Nat.mod_lt _ (by omega)
  exact count_ineq D n ((2*y)%D) ((3*y)%D) ((4*y)%D) ((7*y)%D) (by omega)
    hr2 hr3 hr4 hr7 h_or


