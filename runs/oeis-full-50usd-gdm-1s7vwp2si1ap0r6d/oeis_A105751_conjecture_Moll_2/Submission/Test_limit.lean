import FormalConjectures.Util.ProblemImports

open Complex Filter Asymptotics Topology

noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)


def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

private theorem P_complex (n : ℕ) :
    ((Finset.range (n + 1)).prod (fun k ↦ 1 + (k : ℂ) * I)) = ((P n).1 : ℂ) + ((P n).2 : ℂ) * I := by
  induction n with
  | zero =>
    apply Complex.ext <;> simp [P]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    apply Complex.ext <;> simp [P] <;> ring

theorem a_eq_P_im (n : ℕ) : a n = (P n).2 := by
  unfold a
  dsimp
  rw [P_complex]
  simp

lemma tendsto_sqrt_div_self_atTop : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℚ) / (n : ℚ)) atTop (nhds 0) := sorry

lemma valuation_a_ge_k (n : ℕ) (hn : a n ≠ 0) : padicValInt 2 (a n) ≥ n / 4 := sorry

-- Let's define the upper bound lemma we want to use
lemma valuation_a_le (n : ℕ) : (padicValInt 2 (a n) : ℚ) ≤ (n : ℚ) / 4 + 2 * (Nat.sqrt n : ℚ) + 3 := sorry

lemma a_ne_zero (n : ℕ) (hn : n ≥ 4) : a n ≠ 0 := sorry

def g_seq (n : ℕ) : ℚ :=
  if n < 4 then -1 else 1 - 4 / (n : ℚ)

def h_seq (n : ℕ) : ℚ :=
  if n < 4 then 100 else 1 + 8 * (Nat.sqrt n : ℚ) / (n : ℚ) + 12 / (n : ℚ)

lemma tendsto_g : Tendsto g_seq atTop (nhds 1) := by
  have h_eq : ∀ᶠ (n : ℕ) in atTop, g_seq n = 1 - 4 * (n : ℚ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    unfold g_seq
    split_ifs with h'
    · omega
    · have : (n : ℚ) ≠ 0 := by positivity
      rw [div_eq_mul_inv, mul_comm]
  rw [tendsto_congr' h_eq]
  have h_inv : Tendsto (fun n : ℕ ↦ (n : ℚ)⁻¹) atTop (nhds 0) :=
    Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop
  have h_mul : Tendsto (fun n : ℕ ↦ 4 * (n : ℚ)⁻¹) atTop (nhds (4 * 0)) :=
    Tendsto.const_mul 4 h_inv
  rw [mul_zero] at h_mul
  have h_sub : Tendsto (fun n : ℕ ↦ 1 - 4 * (n : ℚ)⁻¹) atTop (nhds (1 - 0)) :=
    Tendsto.const_sub 1 h_mul
  rw [sub_zero] at h_sub
  exact h_sub

lemma tendsto_h : Tendsto h_seq atTop (nhds 1) := by
  have h_eq : ∀ᶠ (n : ℕ) in atTop, h_seq n = 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ)) + 12 * (n : ℚ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    unfold h_seq
    split_ifs with h'
    · omega
    · have : (n : ℚ) ≠ 0 := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  rw [tendsto_congr' h_eq]
  have h_sqrt : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℚ) / (n : ℚ)) atTop (nhds 0) := tendsto_sqrt_div_self_atTop
  have h_mul1 : Tendsto (fun n : ℕ ↦ 8 * ((Nat.sqrt n : ℚ) / (n : ℚ))) atTop (nhds (8 * 0)) :=
    Tendsto.const_mul 8 h_sqrt
  rw [mul_zero] at h_mul1
  have h_inv : Tendsto (fun n : ℕ ↦ (n : ℚ)⁻¹) atTop (nhds 0) :=
    Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop
  have h_mul2 : Tendsto (fun n : ℕ ↦ 12 * (n : ℚ)⁻¹) atTop (nhds (12 * 0)) :=
    Tendsto.const_mul 12 h_inv
  rw [mul_zero] at h_mul2
  have h_add1 : Tendsto (fun n : ℕ ↦ 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ))) atTop (nhds (1 + 0)) :=
    Tendsto.const_add 1 h_mul1
  rw [add_zero] at h_add1
  have h_add2 : Tendsto (fun n : ℕ ↦ 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ)) + 12 * (n : ℚ)⁻¹) atTop (nhds (1 + 0)) :=
    Tendsto.add h_add1 h_mul2
  rw [add_zero] at h_add2
  exact h_add2

theorem oeis_A105751_conjecture_Moll_2 :
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1) := by
  have h_g : Tendsto g_seq atTop (nhds 1) := tendsto_g
  have h_h : Tendsto h_seq atTop (nhds 1) := tendsto_h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_g h_h
  · intro n
    unfold g_seq
    split_ifs with h
    · -- n < 4
      have h_pos : (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ) ≥ 0 := by positivity
      linarith
    · -- n ≥ 4
      push_neg at h
      have h_pos : (n : ℚ) > 0 := by positivity
      have h_ne : (n : ℚ) ≠ 0 := ne_of_gt h_pos
      have h_v_ge := valuation_a_ge_k n (a_ne_zero n h)
      have h_v_ge_q : (padicValInt 2 (a n) : ℚ) ≥ ((n / 4 : ℕ) : ℚ) := by exact_mod_cast h_v_ge
      have h_div := (Nat.div_add_mod n 4).symm
      have h_div_q : (n : ℚ) = 4 * ((n / 4 : ℕ) : ℚ) + ((n % 4 : ℕ) : ℚ) := by exact_mod_cast h_div
      have h_mod_lt : ((n % 4 : ℕ) : ℚ) < 4 := by
        have : n % 4 < 4 := Nat.mod_lt n (by decide)
        exact_mod_cast this
      have h_mod_ge : ((n % 4 : ℕ) : ℚ) ≥ 0 := by positivity
      have h_div_ge : ((n / 4 : ℕ) : ℚ) ≥ (n : ℚ)/4 - 1 := by linarith
      have h_ge : (padicValInt 2 (a n) : ℚ) ≥ (n : ℚ)/4 - 1 := le_trans h_div_ge h_v_ge_q
      field_simp at *
      linarith
  · intro n
    unfold h_seq
    split_ifs with h
    · -- n < 4
      rcases n with _ | _ | _ | _ | hn
      · -- n = 0
        have h_a0 : a 0 = 0 := by
          rw [a_eq_P_im]
          rfl
        have h_v0 : padicValInt 2 0 = 0 := by
          unfold padicValInt
          rfl
        simp [h_a0, h_v0]
      · -- n = 1
        have h_a1 : a 1 = 1 := by
          rw [a_eq_P_im]
          rfl
        have h_v1 : padicValInt 2 1 = 0 := by
          unfold padicValInt
          apply padicValNat.eq_zero_of_not_dvd
          intro hc
          omega
        simp [h_a1, h_v1]
      · -- n = 2
        have h_a2 : a 2 = 3 := by
          rw [a_eq_P_im]
          rfl
        have h_v2 : padicValInt 2 3 = 0 := by
          unfold padicValInt
          apply padicValNat.eq_zero_of_not_dvd
          intro hc
          omega
        simp [h_a2, h_v2]
      · -- n = 3
        have h_a3 : a 3 = 0 := by
          rw [a_eq_P_im]
          rfl
        have h_v3 : padicValInt 2 0 = 0 := by
          unfold padicValInt
          rfl
        simp [h_a3, h_v3]
      · -- n ≥ 4
        omega
    · -- n ≥ 4
      push_neg at h
      have h_pos : (n : ℚ) > 0 := by positivity
      have h_ne : (n : ℚ) ≠ 0 := ne_of_gt h_pos
      have h_le := valuation_a_le n
      field_simp at *
      linarith
